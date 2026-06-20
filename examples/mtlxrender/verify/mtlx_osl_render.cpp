//
// mtlx_osl_render.cpp - render one MaterialX material through the ASF MaterialX
// OSL path (MaterialXGenOsl -> oslc -> testrender) and write a PNG. This is the
// Phase-2 CPU reference: a real path tracer, the tight apples-to-apples check
// against lightrt's path tracer.
//
// Mirrors MaterialX's own OslShaderRenderTester (source/MaterialXTest/
// MaterialXRenderOsl/RenderOsl.cpp): load the material + data libraries, find a
// renderable element, generate OSL, compile the utility shaders, then drive
// OslRenderer (oslc + testrender) with our scene template and HDR env, and save
// the captured image.
//
// Usage:
//   mtlx_osl_render <material.mtlx> <out.png> <env.hdr> <W> <H>
//                   <materialx_src> <oslc> <testrender> <osl_include>
//                   <utilities_dir> <scene_template.xml>
//
// SPDX-License-Identifier: Apache-2.0
//
#include <iostream>
#include <string>
#include <vector>

#include <MaterialXCore/Document.h>
#include <MaterialXFormat/File.h>
#include <MaterialXFormat/Util.h>
#include <MaterialXFormat/XmlIo.h>

#include <MaterialXGenShader/DefaultColorManagementSystem.h>
#include <MaterialXGenShader/GenContext.h>
#include <MaterialXGenShader/Shader.h>
#include <MaterialXGenShader/Util.h>
#include <MaterialXGenOsl/OslShaderGenerator.h>

#include <MaterialXRender/ImageHandler.h>
#include <MaterialXRender/StbImageLoader.h>
#include <MaterialXRenderOsl/OslRenderer.h>

namespace mx = MaterialX;

static int fail(const std::string& msg)
{
    std::cerr << "mtlx_osl_render: " << msg << std::endl;
    return 1;
}

int main(int argc, char** argv)
{
    if (argc < 12)
        return fail("usage: mtlx_osl_render <mtlx> <out.png> <env.hdr> <W> <H> "
                    "<materialx_src> <oslc> <testrender> <osl_include> "
                    "<utilities_dir> <scene_template.xml>");

    const std::string matFile = argv[1];
    const std::string outPng = argv[2];
    const std::string envHdr = argv[3];
    const unsigned int W = (unsigned int)std::stoi(argv[4]);
    const unsigned int H = (unsigned int)std::stoi(argv[5]);
    const std::string mtlxSrc = argv[6];
    const std::string oslc = argv[7];
    const std::string testrender = argv[8];
    const std::string oslInclude = argv[9];
    const std::string utilDir = argv[10];
    const std::string sceneTemplate = argv[11];

    try
    {
        // ---- search path + data libraries -------------------------------
        mx::FileSearchPath searchPath = mx::getDefaultDataSearchPath();
        searchPath.append(mx::FilePath(mtlxSrc));
        searchPath.append(mx::FilePath(mtlxSrc) / "libraries");

        mx::DocumentPtr stdlib = mx::createDocument();
        mx::FilePathVec libraryFolders = { mx::FilePath("libraries") };
        mx::loadLibraries(libraryFolders, searchPath, stdlib);

        mx::DocumentPtr doc = mx::createDocument();
        doc->importLibrary(stdlib);
        mx::readFromXmlFile(doc, matFile, searchPath);

        std::string err;
        if (!doc->validate(&err))
            std::cerr << "mtlx_osl_render: doc validation warnings: " << err << std::endl;

        // ---- pick a renderable surface shader element -------------------
        std::vector<mx::TypedElementPtr> elems;
        try { elems = mx::findRenderableElements(doc); }
        catch (const std::exception& e) { return fail(std::string("findRenderableElements: ") + e.what()); }
        if (elems.empty())
            return fail("no renderable elements in " + matFile);
        mx::TypedElementPtr elem = elems[0];

        // ---- OSL shader generation --------------------------------------
        mx::ShaderGeneratorPtr gen = mx::OslShaderGenerator::create();
        mx::GenContext context(gen);
        context.registerSourceCodeSearchPath(searchPath);
        mx::DefaultColorManagementSystemPtr cms =
            mx::DefaultColorManagementSystem::create(gen->getTarget());
        cms->loadLibrary(doc);
        context.getShaderGenerator().setColorManagementSystem(cms);
        context.getOptions().fileTextureVerticalFlip = true;

        std::string shaderName = mx::createValidName(elem->getNamePath());
        mx::ShaderPtr shader = gen->generate(shaderName, elem, context);
        if (!shader)
            return fail("OSL shader generation failed for " + shaderName);

        // ---- OSL renderer (oslc + testrender) ---------------------------
        mx::OslRendererPtr renderer = mx::OslRenderer::create(W, H);
        renderer->setOslCompilerExecutable(oslc);
        renderer->setOslTestRenderExecutable(testrender);
        // oslc needs both the OSL stdosl.h dir AND the MaterialX genosl headers
        // (mx_funcs.h et al., under libraries/stdlib/genosl/include) that the
        // generated shader #includes.
        mx::FileSearchPath oslIncPath(oslInclude);
        oslIncPath.append(mx::FilePath(mtlxSrc) / "libraries" / "stdlib" / "genosl" / "include");
        renderer->setOslIncludePath(oslIncPath);

        mx::StbImageLoaderPtr stb = mx::StbImageLoader::create();
        mx::ImageHandlerPtr imageHandler = mx::ImageHandler::create(stb);
        imageHandler->setSearchPath(searchPath);
        renderer->setImageHandler(imageHandler);
        renderer->setLightHandler(nullptr);
        renderer->initialize();

        // Pre-compile the utility OSL shaders (envmap, raytype_background, ...).
        mx::FilePath utils(utilDir);
        renderer->setOslOutputFilePath(utils);
        for (const mx::FilePath& f : utils.getFilesInDirectory("osl"))
            renderer->compileOSL(utils / f);
        renderer->setOslUtilityOSOPath(utils);

        // Compile the generated material shader.
        std::string outDir = mx::FilePath(outPng).getParentPath().asString();
        if (outDir.empty()) outDir = ".";
        renderer->setOslOutputFilePath(mx::FilePath(outDir));
        renderer->setOslShaderName(shaderName);
        // testrender traces AA*AA samples/pixel, so AaLit=16 -> 256 spp. The
        // higher count is needed because the matte/diffuse materials are
        // IBL-noise-dominated at lower sampling (the residual vs lightrt is the
        // path tracer's own Monte-Carlo grain, not a shading difference).
        renderer->setAaLit(16);
        renderer->setAaUnlit(2);
        renderer->createProgram(shader);
        renderer->setSize(W, H);

        // Bind the HDR environment for the IBL.
        mx::StringVec envOverrides;
        envOverrides.push_back("string envmap_filename \"" + envHdr + "\";\n");
        renderer->setEnvShaderParameterOverrides(envOverrides);

        // Output port name/type, scene template.
        const mx::ShaderStage& stage = shader->getStage(mx::Stage::PIXEL);
        const mx::VariableBlock& outputs = stage.getOutputBlock(mx::OSL::OUTPUTS);
        if (outputs.empty())
            return fail("generated OSL shader has no output block");
        const mx::ShaderPort* output = outputs[0];
        const mx::TypeSyntax& ts = gen->getSyntax().getTypeSyntax(output->getType());
        const std::string outName = output->getVariable();
        const std::string outType = ts.getTypeAlias().empty() ? ts.getName() : ts.getTypeAlias();
        renderer->setOslShaderOutput(outName, outType);
        renderer->setOslTestRenderSceneTemplateFile(sceneTemplate);

        renderer->render();
        mx::ImagePtr image = renderer->captureImage();
        if (!image)
            return fail("captureImage returned null");

        // testrender's captured framebuffer has a bottom-up origin; save without
        // the loader's extra vertical flip so the PNG is top-down like the lightrt
        // and GLSL renders (verified: chrome reflection aligns, masked-RMSE 0.35
        // -> 0.009). This matches MaterialX's own OslShaderRenderTester::saveImage,
        // which also passes verticalFlip=false.
        if (!imageHandler->saveImage(mx::FilePath(outPng), image, false))
            return fail("failed to save " + outPng);

        std::cout << "mtlx_osl_render: wrote " << outPng << " (" << W << "x" << H
                  << ", shader " << shaderName << ")" << std::endl;
        return 0;
    }
    catch (const std::exception& e)
    {
        return fail(std::string("exception: ") + e.what());
    }
}
