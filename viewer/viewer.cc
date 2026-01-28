#define TINYOBJLOADER_IMPLEMENTATION
#define TINYGLTF_IMPLEMENTATION
#define STB_IMAGE_IMPLEMENTATION
#define STB_IMAGE_WRITE_IMPLEMENTATION
#define TINYGLTF_NO_INCLUDE_STB_IMAGE
#define TINYGLTF_NO_INCLUDE_STB_IMAGE_WRITE
#define TINYGLTF_NO_INCLUDE_JSON

#include "third_party/json.hpp"
#include "third_party/stb_image.h"
#include "third_party/stb_image_write.h"
#include "third_party/tiny_obj_loader.h"
#include "third_party/tiny_gltf.h"

// Include Vulkan Loader FIRST so GLFW sees the types
#include "vk_loader.h"
#include <GLFW/glfw3.h>

#include "../lightrt.hh"
#include "bitmap_font.h"

#include <iostream>
#include <vector>
#include <string>
#include <chrono>
#include <thread>
#include <mutex>
#include <algorithm>
#include <cmath>

using namespace lightrt;

// --- Data Structures ---

struct SimpleMesh {
    std::vector<Triangle> triangles;
    TriangleBVH bvh;
};

struct Camera {
    Vec3 position{0, 0, 5};
    Vec3 forward{0, 0, -1};
    Vec3 up{0, 1, 0};
    Vec3 right{1, 0, 0};
    float fov = 60.0f;
    float yaw = -90.0f;
    float pitch = 0.0f;
};

// --- Global State ---
SimpleMesh g_mesh;
Camera g_camera;
uint32_t g_width = 1280;
uint32_t g_height = 720;
bool g_keys[1024] = {0};
double g_lastX = 0, g_lastY = 0;
bool g_firstMouse = true;
bool g_mouseCaptured = false;
int g_renderMode = 0;  // 0=solid, 1=wireframe, 2=overlay

// --- Loader Functions ---

bool LoadOBJ(const std::string& filename, SimpleMesh& mesh) {
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    std::string warn, err;

    if (!tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err, filename.c_str())) {
        std::cerr << "TinyObj Error: " << warn << err << "\n";
        return false;
    }

    for (const auto& shape : shapes) {
        size_t index_offset = 0;
        for (size_t f = 0; f < shape.mesh.num_face_vertices.size(); f++) {
            int fv = shape.mesh.num_face_vertices[f];
            if (fv == 3) {
                tinyobj::index_t idx0 = shape.mesh.indices[index_offset + 0];
                tinyobj::index_t idx1 = shape.mesh.indices[index_offset + 1];
                tinyobj::index_t idx2 = shape.mesh.indices[index_offset + 2];

                Vec3 v0(attrib.vertices[3 * idx0.vertex_index + 0], attrib.vertices[3 * idx0.vertex_index + 1], attrib.vertices[3 * idx0.vertex_index + 2]);
                Vec3 v1(attrib.vertices[3 * idx1.vertex_index + 0], attrib.vertices[3 * idx1.vertex_index + 1], attrib.vertices[3 * idx1.vertex_index + 2]);
                Vec3 v2(attrib.vertices[3 * idx2.vertex_index + 0], attrib.vertices[3 * idx2.vertex_index + 1], attrib.vertices[3 * idx2.vertex_index + 2]);

                Triangle tri;
                tri.v0 = v0;
                tri.v1 = v1;
                tri.v2 = v2;
                mesh.triangles.push_back(tri);
            }
            index_offset += fv;
        }
    }
    return true;
}

bool LoadGLTF(const std::string& filename, SimpleMesh& mesh) {
    tinygltf::Model model;
    tinygltf::TinyGLTF loader;
    std::string err, warn;

    bool ret;
    if (filename.find(".glb") != std::string::npos) {
         ret = loader.LoadBinaryFromFile(&model, &err, &warn, filename);
    } else {
         ret = loader.LoadASCIIFromFile(&model, &err, &warn, filename);
    }

    if (!warn.empty()) std::cout << "GLTF Warn: " << warn << "\n";
    if (!err.empty()) std::cout << "GLTF Err: " << err << "\n";
    if (!ret) return false;

    // Minimal GLTF loader
    for (const auto& meshIdx : model.meshes) {
        for (const auto& primitive : meshIdx.primitives) {
            const float* positionBuffer = nullptr;
            const unsigned char* indexBuffer = nullptr;
            int posStride = 0;
            int idxType = 0;
            size_t indexCount = 0;

            auto it = primitive.attributes.find("POSITION");
            if (it != primitive.attributes.end()) {
                const auto& accessor = model.accessors[it->second];
                const auto& view = model.bufferViews[accessor.bufferView];
                positionBuffer = reinterpret_cast<const float*>(&model.buffers[view.buffer].data[accessor.byteOffset + view.byteOffset]);
                posStride = accessor.ByteStride(view) / sizeof(float);
            }

            if (primitive.indices >= 0) {
                const auto& accessor = model.accessors[primitive.indices];
                const auto& view = model.bufferViews[accessor.bufferView];
                indexBuffer = &model.buffers[view.buffer].data[accessor.byteOffset + view.byteOffset];
                idxType = accessor.componentType;
                indexCount = accessor.count;
            }

            if (positionBuffer && indexCount > 0) {
                for (size_t i = 0; i < indexCount; i += 3) {
                    uint32_t i0 = 0, i1 = 0, i2 = 0;
                    if (idxType == TINYGLTF_COMPONENT_TYPE_UNSIGNED_SHORT) {
                        const uint16_t* buf = (const uint16_t*)indexBuffer;
                        i0 = buf[i]; i1 = buf[i+1]; i2 = buf[i+2];
                    } else if (idxType == TINYGLTF_COMPONENT_TYPE_UNSIGNED_INT) {
                        const uint32_t* buf = (const uint32_t*)indexBuffer;
                        i0 = buf[i]; i1 = buf[i+1]; i2 = buf[i+2];
                    } else if (idxType == TINYGLTF_COMPONENT_TYPE_UNSIGNED_BYTE) {
                         const uint8_t* buf = (const uint8_t*)indexBuffer;
                         i0 = buf[i]; i1 = buf[i+1]; i2 = buf[i+2];
                    }

                    Vec3 v0(positionBuffer[i0 * posStride], positionBuffer[i0 * posStride + 1], positionBuffer[i0 * posStride + 2]);
                    Vec3 v1(positionBuffer[i1 * posStride], positionBuffer[i1 * posStride + 1], positionBuffer[i1 * posStride + 2]);
                    Vec3 v2(positionBuffer[i2 * posStride], positionBuffer[i2 * posStride + 1], positionBuffer[i2 * posStride + 2]);
                    Triangle tri; tri.v0 = v0; tri.v1 = v1; tri.v2 = v2;
                    mesh.triangles.push_back(tri);
                }
            }
        }
    }
    return true;
}

// --- Vulkan Renderer (Minimal Transfer Only) ---

struct VulkanContext {
    VkInstance instance;
    VkPhysicalDevice physicalDevice;
    VkDevice device;
    VkQueue queue;
    VkSurfaceKHR surface;
    VkSwapchainKHR swapchain;
    std::vector<VkImage> swapchainImages;
    VkCommandPool commandPool;
    VkCommandBuffer commandBuffer;
    VkSemaphore imageAvailableSemaphore;
    VkSemaphore renderFinishedSemaphore;
    VkFence renderFence;

    VkBuffer stagingBuffer;
    VkDeviceMemory stagingMemory;
    void* mappedMemory;

    uint32_t width, height;

    void Check(VkResult result, const char* msg) {
        if (result != VK_SUCCESS) {
            std::cerr << "Vulkan Error: " << msg << " (" << result << ")\n";
            exit(1);
        }
    }

    void Init(GLFWwindow* window, uint32_t w, uint32_t h) {
        width = w; height = h;
        LoadVulkan();

        // 1. Instance
        VkApplicationInfo appInfo = {VK_STRUCTURE_TYPE_APPLICATION_INFO, nullptr, "Viewer", 1, "No Engine", 1, VK_API_VERSION_1_1};
        
        uint32_t glfwExtCount = 0;
        const char** glfwExts = glfwGetRequiredInstanceExtensions(&glfwExtCount);
        
        VkInstanceCreateInfo createInfo = {VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO};
        createInfo.pApplicationInfo = &appInfo;
        createInfo.enabledExtensionCount = glfwExtCount;
        createInfo.ppEnabledExtensionNames = glfwExts;

        Check(vkCreateInstance(&createInfo, nullptr, &instance), "Create Instance");
        LoadInstanceFunctions(instance);

        // 2. Surface
        if (glfwCreateWindowSurface(instance, window, nullptr, &surface) != VK_SUCCESS) {
            std::cerr << "Failed to create window surface\n"; exit(1);
        }

        // 3. Physical Device
        uint32_t count = 0;
        vkEnumeratePhysicalDevices(instance, &count, nullptr);
        std::vector<VkPhysicalDevice> devices(count);
        vkEnumeratePhysicalDevices(instance, &count, devices.data());
        physicalDevice = devices[0]; 

        // 4. Device
        float queuePriority = 1.0f;
        VkDeviceQueueCreateInfo queueInfo = {VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO};
        queueInfo.queueFamilyIndex = 0; 
        queueInfo.queueCount = 1;
        queueInfo.pQueuePriorities = &queuePriority;
        
        const char* deviceExts[] = { "VK_KHR_swapchain" };
        VkDeviceCreateInfo devInfo = {VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO};
        devInfo.pQueueCreateInfos = &queueInfo;
        devInfo.queueCreateInfoCount = 1;
        devInfo.enabledExtensionCount = 1;
        devInfo.ppEnabledExtensionNames = deviceExts;

        Check(vkCreateDevice(physicalDevice, &devInfo, nullptr, &device), "Create Device");
        LoadDeviceFunctions(device);
        vkGetDeviceQueue(device, 0, 0, &queue);

        // 5. Swapchain
        VkSwapchainCreateInfoKHR swapchainInfo = {VK_STRUCTURE_TYPE_SWAPCHAIN_CREATE_INFO_KHR};
        swapchainInfo.surface = surface;
        swapchainInfo.minImageCount = 2;
        swapchainInfo.imageFormat = VK_FORMAT_B8G8R8A8_UNORM;
        swapchainInfo.imageColorSpace = VK_COLOR_SPACE_SRGB_NONLINEAR_KHR;
        swapchainInfo.imageExtent = {width, height};
        swapchainInfo.imageArrayLayers = 1;
        swapchainInfo.imageUsage = VK_IMAGE_USAGE_TRANSFER_DST_BIT; 
        swapchainInfo.preTransform = VK_SURFACE_TRANSFORM_IDENTITY_BIT_KHR;
        swapchainInfo.compositeAlpha = VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR;
        swapchainInfo.presentMode = VK_PRESENT_MODE_FIFO_KHR;
        swapchainInfo.clipped = VK_TRUE;

        Check(vkCreateSwapchainKHR(device, &swapchainInfo, nullptr, &swapchain), "Create Swapchain");

        vkGetSwapchainImagesKHR(device, swapchain, &count, nullptr);
        swapchainImages.resize(count);
        vkGetSwapchainImagesKHR(device, swapchain, &count, swapchainImages.data());

        // 6. Commands & Sync
        VkCommandPoolCreateInfo poolInfo = {VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO};
        poolInfo.queueFamilyIndex = 0;
        poolInfo.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
        vkCreateCommandPool(device, &poolInfo, nullptr, &commandPool);

        VkCommandBufferAllocateInfo allocInfo = {VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO};
        allocInfo.commandPool = commandPool;
        allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
        allocInfo.commandBufferCount = 1;
        vkAllocateCommandBuffers(device, &allocInfo, &commandBuffer);

        VkSemaphoreCreateInfo semInfo = {VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO};
        vkCreateSemaphore(device, &semInfo, nullptr, &imageAvailableSemaphore);
        vkCreateSemaphore(device, &semInfo, nullptr, &renderFinishedSemaphore);

        VkFenceCreateInfo fenceInfo = {VK_STRUCTURE_TYPE_FENCE_CREATE_INFO};
        fenceInfo.flags = VK_FENCE_CREATE_SIGNALED_BIT;
        vkCreateFence(device, &fenceInfo, nullptr, &renderFence);

        // 7. Staging Buffer
        VkBufferCreateInfo bufInfo = {VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO};
        bufInfo.size = width * height * 4;
        bufInfo.usage = VK_BUFFER_USAGE_TRANSFER_SRC_BIT;
        vkCreateBuffer(device, &bufInfo, nullptr, &stagingBuffer);

        VkMemoryRequirements memReq;
        vkGetBufferMemoryRequirements(device, stagingBuffer, &memReq);
        
        VkPhysicalDeviceMemoryProperties memProps;
        vkGetPhysicalDeviceMemoryProperties(physicalDevice, &memProps);

        uint32_t memTypeIndex = 0;
        for (uint32_t i=0; i<memProps.memoryTypeCount; i++) {
            if ((memReq.memoryTypeBits & (1 << i)) && 
                (memProps.memoryTypes[i].propertyFlags & (VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT))) {
                memTypeIndex = i;
                break;
            }
        }

        VkMemoryAllocateInfo memAlloc = {VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO};
        memAlloc.allocationSize = memReq.size;
        memAlloc.memoryTypeIndex = memTypeIndex;
        vkAllocateMemory(device, &memAlloc, nullptr, &stagingMemory);
        vkBindBufferMemory(device, stagingBuffer, stagingMemory, 0);
        vkMapMemory(device, stagingMemory, 0, memReq.size, 0, &mappedMemory);
    }

    void Present(const std::vector<uint32_t>& pixels) {
        vkWaitForFences(device, 1, &renderFence, VK_TRUE, UINT64_MAX);
        vkResetFences(device, 1, &renderFence);

        uint32_t imageIndex;
        VkResult res = vkAcquireNextImageKHR(device, swapchain, UINT64_MAX, imageAvailableSemaphore, VK_NULL_HANDLE, &imageIndex);
        if (res != VK_SUCCESS) return;

        memcpy(mappedMemory, pixels.data(), pixels.size() * sizeof(uint32_t));

        VkCommandBufferBeginInfo beginInfo = {VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO};
        vkBeginCommandBuffer(commandBuffer, &beginInfo);

        VkImageMemoryBarrier barrier1 = {VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER};
        barrier1.oldLayout = VK_IMAGE_LAYOUT_UNDEFINED;
        barrier1.newLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
        barrier1.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
        barrier1.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
        barrier1.image = swapchainImages[imageIndex];
        barrier1.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        barrier1.subresourceRange.levelCount = 1;
        barrier1.subresourceRange.layerCount = 1;
        barrier1.srcAccessMask = 0;
        barrier1.dstAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;

        vkCmdPipelineBarrier(commandBuffer, VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT, 0, 0, nullptr, 0, nullptr, 1, &barrier1);

        VkBufferImageCopy region = {};
        region.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        region.imageSubresource.layerCount = 1;
        region.imageExtent = {width, height, 1};
        vkCmdCopyBufferToImage(commandBuffer, stagingBuffer, swapchainImages[imageIndex], VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, 1, &region);

        VkImageMemoryBarrier barrier2 = barrier1;
        barrier2.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
        barrier2.newLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;
        barrier2.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier2.dstAccessMask = VK_ACCESS_MEMORY_READ_BIT;

        vkCmdPipelineBarrier(commandBuffer, VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_BOTTOM_OF_PIPE_BIT, 0, 0, nullptr, 0, nullptr, 1, &barrier2);

        vkEndCommandBuffer(commandBuffer);

        VkSubmitInfo submitInfo = {VK_STRUCTURE_TYPE_SUBMIT_INFO};
        VkPipelineStageFlags waitStages[] = {VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT};
        submitInfo.waitSemaphoreCount = 1;
        submitInfo.pWaitSemaphores = &imageAvailableSemaphore;
        submitInfo.pWaitDstStageMask = waitStages;
        submitInfo.commandBufferCount = 1;
        submitInfo.pCommandBuffers = &commandBuffer;
        submitInfo.signalSemaphoreCount = 1;
        submitInfo.pSignalSemaphores = &renderFinishedSemaphore;

        vkQueueSubmit(queue, 1, &submitInfo, renderFence);

        VkPresentInfoKHR presentInfo = {VK_STRUCTURE_TYPE_PRESENT_INFO_KHR};
        presentInfo.waitSemaphoreCount = 1;
        presentInfo.pWaitSemaphores = &renderFinishedSemaphore;
        presentInfo.swapchainCount = 1;
        presentInfo.pSwapchains = &swapchain;
        presentInfo.pImageIndices = &imageIndex;

        vkQueuePresentKHR(queue, &presentInfo);
    }
};

// --- Application Logic ---

static bool g_fKeyWasPressed = false;

void processInput(GLFWwindow* window, float dt) {
    if (glfwGetKey(window, GLFW_KEY_ESCAPE) == GLFW_PRESS)
        glfwSetWindowShouldClose(window, true);

    float speed = 2.5f * dt;
    if (glfwGetKey(window, GLFW_KEY_W) == GLFW_PRESS) g_camera.position = g_camera.position + g_camera.forward * speed;
    if (glfwGetKey(window, GLFW_KEY_S) == GLFW_PRESS) g_camera.position = g_camera.position - g_camera.forward * speed;
    if (glfwGetKey(window, GLFW_KEY_A) == GLFW_PRESS) g_camera.position = g_camera.position - g_camera.right * speed;
    if (glfwGetKey(window, GLFW_KEY_D) == GLFW_PRESS) g_camera.position = g_camera.position + g_camera.right * speed;

    // Toggle render mode with F key (solid -> wireframe -> overlay -> solid)
    bool fKeyPressed = glfwGetKey(window, GLFW_KEY_F) == GLFW_PRESS;
    if (fKeyPressed && !g_fKeyWasPressed) {
        g_renderMode = (g_renderMode + 1) % 3;
    }
    g_fKeyWasPressed = fKeyPressed;
}

void mouse_callback(GLFWwindow* window, double xpos, double ypos) {
    (void)window;
    if (!g_mouseCaptured) return;
    if (g_firstMouse) {
        g_lastX = xpos;
        g_lastY = ypos;
        g_firstMouse = false;
    }

    float xoffset = xpos - g_lastX;
    float yoffset = g_lastY - ypos; 
    g_lastX = xpos;
    g_lastY = ypos;

    float sensitivity = 0.1f;
    xoffset *= sensitivity;
    yoffset *= sensitivity;

    g_camera.yaw += xoffset;
    g_camera.pitch += yoffset;

    if (g_camera.pitch > 89.0f) g_camera.pitch = 89.0f;
    if (g_camera.pitch < -89.0f) g_camera.pitch = -89.0f;

    Vec3 front;
    front.x = cos(g_camera.yaw * 3.14159f / 180.0f) * cos(g_camera.pitch * 3.14159f / 180.0f);
    front.y = sin(g_camera.pitch * 3.14159f / 180.0f);
    front.z = sin(g_camera.yaw * 3.14159f / 180.0f) * cos(g_camera.pitch * 3.14159f / 180.0f);
    g_camera.forward = front.normalize();
    g_camera.right = g_camera.forward.cross(Vec3(0, 1, 0)).normalize();
    g_camera.up = g_camera.right.cross(g_camera.forward).normalize();
}

void mouse_button_callback(GLFWwindow* window, int button, int action, int mods) {
    (void)mods;
    if (button == GLFW_MOUSE_BUTTON_LEFT && action == GLFW_PRESS) {
        g_mouseCaptured = !g_mouseCaptured;
        if (g_mouseCaptured) {
            glfwSetInputMode(window, GLFW_CURSOR, GLFW_CURSOR_DISABLED);
            g_firstMouse = true;
        } else {
            glfwSetInputMode(window, GLFW_CURSOR, GLFW_CURSOR_NORMAL);
        }
    }
}

// Project 3D world point to screen coordinates
// Returns false if point is behind camera
bool projectToScreen(const Vec3& worldPos, const Camera& cam,
                     int width, int height, int& screenX, int& screenY) {
    // Transform to camera space
    Vec3 toPoint = worldPos - cam.position;

    // Project onto camera axes
    float z = toPoint.dot(cam.forward);  // depth
    if (z <= 0.001f) return false;  // Behind camera

    float x = toPoint.dot(cam.right);
    float y = toPoint.dot(cam.up);

    // Perspective projection
    float aspectRatio = (float)width / height;
    float scale = tan(cam.fov * 0.5f * 3.14159f / 180.0f);

    float ndcX = x / (z * aspectRatio * scale);
    float ndcY = y / (z * scale);

    // NDC to screen coordinates
    screenX = (int)((ndcX + 1.0f) * 0.5f * width);
    screenY = (int)((1.0f - ndcY) * 0.5f * height);  // Y is flipped

    return true;
}

// Bresenham's line algorithm with bounds checking
void drawLine(std::vector<uint32_t>& buffer, int width, int height,
              int x0, int y0, int x1, int y1, uint32_t color) {
    // Cohen-Sutherland clipping regions
    auto computeCode = [width, height](int x, int y) -> int {
        int code = 0;
        if (x < 0) code |= 1;       // left
        if (x >= width) code |= 2;  // right
        if (y < 0) code |= 4;       // top
        if (y >= height) code |= 8; // bottom
        return code;
    };

    int code0 = computeCode(x0, y0);
    int code1 = computeCode(x1, y1);

    // Simple rejection: both points outside on same side
    if (code0 & code1) return;

    // Clip line to screen bounds (simplified)
    auto clipLine = [&]() -> bool {
        for (int i = 0; i < 4; i++) {
            if (code0 == 0 && code1 == 0) return true;
            if (code0 & code1) return false;

            int code = code0 ? code0 : code1;
            int x, y;

            if (code & 8) {  // below
                x = x0 + (x1 - x0) * (height - 1 - y0) / (y1 - y0);
                y = height - 1;
            } else if (code & 4) {  // above
                x = x0 + (x1 - x0) * (0 - y0) / (y1 - y0);
                y = 0;
            } else if (code & 2) {  // right
                y = y0 + (y1 - y0) * (width - 1 - x0) / (x1 - x0);
                x = width - 1;
            } else {  // left
                y = y0 + (y1 - y0) * (0 - x0) / (x1 - x0);
                x = 0;
            }

            if (code == code0) {
                x0 = x; y0 = y;
                code0 = computeCode(x0, y0);
            } else {
                x1 = x; y1 = y;
                code1 = computeCode(x1, y1);
            }
        }
        return code0 == 0 && code1 == 0;
    };

    if (!clipLine()) return;

    // Bresenham's algorithm
    int dx = abs(x1 - x0);
    int dy = abs(y1 - y0);
    int sx = x0 < x1 ? 1 : -1;
    int sy = y0 < y1 ? 1 : -1;
    int err = dx - dy;

    while (true) {
        if (x0 >= 0 && x0 < width && y0 >= 0 && y0 < height) {
            buffer[y0 * width + x0] = color;
        }

        if (x0 == x1 && y0 == y1) break;

        int e2 = 2 * err;
        if (e2 > -dy) {
            err -= dy;
            x0 += sx;
        }
        if (e2 < dx) {
            err += dx;
            y0 += sy;
        }
    }
}

// Render wireframe edges of all triangles
void RenderWireframe(std::vector<uint32_t>& buffer, int width, int height,
                     const Camera& cam, uint32_t edgeColor) {
    for (const auto& tri : g_mesh.triangles) {
        int sx0 = 0, sy0 = 0, sx1 = 0, sy1 = 0, sx2 = 0, sy2 = 0;

        bool v0_visible = projectToScreen(tri.v0, cam, width, height, sx0, sy0);
        bool v1_visible = projectToScreen(tri.v1, cam, width, height, sx1, sy1);
        bool v2_visible = projectToScreen(tri.v2, cam, width, height, sx2, sy2);

        // Draw edges only if both vertices are in front of camera
        if (v0_visible && v1_visible)
            drawLine(buffer, width, height, sx0, sy0, sx1, sy1, edgeColor);
        if (v1_visible && v2_visible)
            drawLine(buffer, width, height, sx1, sy1, sx2, sy2, edgeColor);
        if (v2_visible && v0_visible)
            drawLine(buffer, width, height, sx2, sy2, sx0, sy0, edgeColor);
    }
}

void RayTrace(std::vector<uint32_t>& buffer, int width, int height) {
    float invWidth = 1.0f / width;
    float invHeight = 1.0f / height;
    float aspectRatio = (float)width / height;
    float scale = tan(g_camera.fov * 0.5f * 3.14159f / 180.0f);

    int num_threads = std::thread::hardware_concurrency();
    std::vector<std::thread> threads;
    int rows_per_thread = height / num_threads;

    for (int t = 0; t < num_threads; ++t) {
        threads.emplace_back([&, t]() {
            int start_y = t * rows_per_thread;
            int end_y = (t == num_threads - 1) ? height : (t + 1) * rows_per_thread;

            for (int y = start_y; y < end_y; ++y) {
                for (int x = 0; x < width; ++x) {
                    float px = (2 * (x + 0.5f) * invWidth - 1) * aspectRatio * scale;
                    float py = (1 - 2 * (y + 0.5f) * invHeight) * scale;

                    Vec3 dir = (g_camera.forward + g_camera.right * px + g_camera.up * py).normalize();
                    Ray ray(g_camera.position, dir);

                    float t_hit, u, v;
                    uint32_t hit_prim = g_mesh.bvh.traverse(ray, t_hit, u, v);
                    
                    uint32_t color = 0xFF111111; // Dark gray background
                    if (hit_prim != kInvalidIndex) {
                        const Triangle& tri = g_mesh.triangles[hit_prim];
                        Vec3 normal = (tri.v1 - tri.v0).cross(tri.v2 - tri.v0).normalize();
                        float diff = std::max(0.0f, normal.dot(Vec3(0, 1, 0)));
                        
                        // Fake color
                        int r = (hit_prim * 123) % 255;
                        int g = (hit_prim * 456) % 255;
                        int b = (hit_prim * 789) % 255;
                        
                        r = std::min(255, (int)(r * (0.2f + 0.8f * diff)));
                        g = std::min(255, (int)(g * (0.2f + 0.8f * diff)));
                        b = std::min(255, (int)(b * (0.2f + 0.8f * diff)));

                        color = 0xFF000000 | (r << 16) | (g << 8) | b;
                    }

                    buffer[y * width + x] = color;
                }
            }
        });
    }

    for (auto& th : threads) th.join();
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <model.obj/gltf/glb>\n";
        return 1;
    }

    std::string path = argv[1];
    std::cout << "Loading " << path << "...\n";

    bool loaded = false;
    if (path.find(".obj") != std::string::npos) loaded = LoadOBJ(path, g_mesh);
    else loaded = LoadGLTF(path, g_mesh);

    if (!loaded || g_mesh.triangles.empty()) {
        std::cerr << "Failed to load model or empty.\n";
        return 1;
    }

    std::cout << "Building BVH for " << g_mesh.triangles.size() << " triangles...\n";
    BVHBuildConfig config;
    g_mesh.bvh.build(g_mesh.triangles, config);
    std::cout << "BVH Built.\n";

    if (!glfwInit()) return 1;
    glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
    GLFWwindow* window = glfwCreateWindow(g_width, g_height, "LightRT Viewer", nullptr, nullptr);
    glfwSetCursorPosCallback(window, mouse_callback);
    glfwSetMouseButtonCallback(window, mouse_button_callback);

    VulkanContext vk;
    vk.Init(window, g_width, g_height);

    std::vector<uint32_t> pixels(g_width * g_height);

    auto lastTime = std::chrono::high_resolution_clock::now();
    int frameCount = 0;
    float fps = 0;

    std::cout << "Controls: WASD + Mouse (Click to capture/release)\n";

    while (!glfwWindowShouldClose(window)) {
        glfwPollEvents();

        auto currentTime = std::chrono::high_resolution_clock::now();
        std::chrono::duration<float> dt = currentTime - lastTime;
        
        if (dt.count() >= 1.0f) {
            fps = frameCount / dt.count();
            frameCount = 0;
            lastTime = currentTime;
        }

        processInput(window, 0.016f);

        // Render based on mode
        if (g_renderMode == 0 || g_renderMode == 2) {
            // Solid shading
            RayTrace(pixels, g_width, g_height);
        }
        if (g_renderMode == 1) {
            // Wireframe only - clear to dark background
            std::fill(pixels.begin(), pixels.end(), 0xFF111111);
        }
        if (g_renderMode == 1 || g_renderMode == 2) {
            // Draw wireframe edges (green)
            RenderWireframe(pixels, g_width, g_height, g_camera, 0xFF00FF00);
        }

        std::string stats = "FPS: " + std::to_string((int)fps);
        DrawString(10, 10, stats.c_str(), 0xFFFFFFFF, pixels.data(), g_width, g_height);
        
        std::string tris = "Tris: " + std::to_string(g_mesh.triangles.size());
        DrawString(10, 25, tris.c_str(), 0xFFFFFFFF, pixels.data(), g_width, g_height);
        
        const char* modeNames[] = {"Solid", "Wire", "Overlay"};
        std::string help = "WASD Move, Click Mouse Capture, F: Mode [" + std::string(modeNames[g_renderMode]) + "]";
        DrawString(10, g_height - 20, help.c_str(), 0xFFFFFF00, pixels.data(), g_width, g_height);

        vk.Present(pixels);
        frameCount++;
    }

    vkDeviceWaitIdle(vk.device);
    glfwDestroyWindow(window);
    glfwTerminate();

    return 0;
}