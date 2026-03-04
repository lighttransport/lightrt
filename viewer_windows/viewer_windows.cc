// Pure Win32 + GDI viewer — no GLFW, no Vulkan, no external deps beyond lightrt

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <shellapi.h>
#include <commdlg.h>

#include "common/viewer_common.h"

#include <iostream>
#include <string>

using namespace lightrt_viewer;

// --- Globals ---
static ViewerState g_state;
static BITMAPINFO  g_bmi;
static bool        g_running = true;
static LARGE_INTEGER g_perfFreq;
static LARGE_INTEGER g_lastTime;

// --- Helpers ---

static void LoadAndReplaceScene(HWND hwnd, const std::string& path) {
    std::cout << "Loading " << path << "...\n";

    scene::Scene newScene;
    if (!LoadModel(path, newScene)) {
        std::cerr << "Failed to load: " << path << "\n";
        MessageBoxA(hwnd, ("Failed to load:\n" + path).c_str(), "Load Error", MB_OK | MB_ICONERROR);
        return;
    }

    if (sceneTriangleCount(newScene) == 0) {
        std::cerr << "No triangles in: " << path << "\n";
        MessageBoxA(hwnd, "File contains no triangles.", "Load Error", MB_OK | MB_ICONWARNING);
        return;
    }

    g_state.scene = std::move(newScene);
    FitToScene(g_state);

    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << sceneTriangleCount(g_state.scene) << " triangles.\n";

    // Update window title
    std::wstring title = L"LightRT Viewer - ";
    // Extract filename from path
    size_t sep = path.find_last_of("/\\");
    std::string fname = (sep != std::string::npos) ? path.substr(sep + 1) : path;
    int wlen = MultiByteToWideChar(CP_UTF8, 0, fname.c_str(), -1, nullptr, 0);
    std::wstring wfname(wlen - 1, L'\0');
    MultiByteToWideChar(CP_UTF8, 0, fname.c_str(), -1, &wfname[0], wlen);
    title += wfname;
    SetWindowTextW(hwnd, title.c_str());
}

static void ShowOpenFileDialog(HWND hwnd) {
    wchar_t filePath[MAX_PATH] = {};

    // Build filter string (double-null terminated)
    std::wstring filter;
    filter += L"All Supported";
    filter.push_back(L'\0');
#ifdef LIGHTRT_HAS_TINYUSDZ
    filter += L"*.obj;*.gltf;*.glb;*.usd;*.usda;*.usdc;*.usdz";
#else
    filter += L"*.obj;*.gltf;*.glb";
#endif
    filter.push_back(L'\0');
    filter += L"OBJ (*.obj)";
    filter.push_back(L'\0');
    filter += L"*.obj";
    filter.push_back(L'\0');
    filter += L"glTF (*.gltf;*.glb)";
    filter.push_back(L'\0');
    filter += L"*.gltf;*.glb";
    filter.push_back(L'\0');
#ifdef LIGHTRT_HAS_TINYUSDZ
    filter += L"USD (*.usd;*.usda;*.usdc;*.usdz)";
    filter.push_back(L'\0');
    filter += L"*.usd;*.usda;*.usdc;*.usdz";
    filter.push_back(L'\0');
#endif
    filter += L"All Files (*.*)";
    filter.push_back(L'\0');
    filter += L"*.*";
    filter.push_back(L'\0');
    filter.push_back(L'\0'); // final double-null

    OPENFILENAMEW ofn = {};
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner   = hwnd;
    ofn.lpstrFilter  = filter.c_str();
    ofn.lpstrFile    = filePath;
    ofn.nMaxFile     = MAX_PATH;
    ofn.Flags        = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_NOCHANGEDIR;

    if (GetOpenFileNameW(&ofn)) {
        int len = WideCharToMultiByte(CP_UTF8, 0, filePath, -1, nullptr, 0, nullptr, nullptr);
        std::string utf8Path(len - 1, '\0');
        WideCharToMultiByte(CP_UTF8, 0, filePath, -1, &utf8Path[0], len, nullptr, nullptr);
        LoadAndReplaceScene(hwnd, utf8Path);
    }
}

static void UpdateBitmapInfo() {
    memset(&g_bmi, 0, sizeof(g_bmi));
    g_bmi.bmiHeader.biSize        = sizeof(BITMAPINFOHEADER);
    g_bmi.bmiHeader.biWidth       = (LONG)g_state.width;
    g_bmi.bmiHeader.biHeight      = -(LONG)g_state.height; // top-down
    g_bmi.bmiHeader.biPlanes      = 1;
    g_bmi.bmiHeader.biBitCount    = 32;
    g_bmi.bmiHeader.biCompression = BI_RGB;
}

// --- Window Procedure ---

static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_DESTROY:
        g_running = false;
        PostQuitMessage(0);
        return 0;

    case WM_SIZE: {
        uint32_t w = LOWORD(lParam);
        uint32_t h = HIWORD(lParam);
        if (w > 0 && h > 0 && (w != g_state.width || h != g_state.height)) {
            ResizeFramebuffer(g_state, w, h);
            UpdateBitmapInfo();
        }
        return 0;
    }

    case WM_KEYDOWN: {
        switch (wParam) {
        case 'F':        g_state.keys[KEY_F] = true; break;
        case 'S':        g_state.keys[KEY_S] = true; break;
        case 'O':        ShowOpenFileDialog(hwnd); break;
        case VK_OEM_PLUS: g_state.keys[KEY_PLUS] = true; break;
        case VK_ESCAPE:  g_state.keys[KEY_ESCAPE] = true; break;
        case VK_TAB:     g_state.tabPressed = true; break;
        case VK_SHIFT:   g_state.shiftPressed = true; break;
        case VK_CONTROL: g_state.ctrlPressed = true; break;
        }
        return 0;
    }

    case WM_KEYUP: {
        switch (wParam) {
        case 'F':        g_state.keys[KEY_F] = false; break;
        case 'S':        g_state.keys[KEY_S] = false; break;
        case VK_OEM_PLUS: g_state.keys[KEY_PLUS] = false; break;
        case VK_ESCAPE:  g_state.keys[KEY_ESCAPE] = false; break;
        case VK_TAB:     g_state.tabPressed = false; break;
        case VK_SHIFT:   g_state.shiftPressed = false; break;
        case VK_CONTROL: g_state.ctrlPressed = false; break;
        }
        return 0;
    }

    // Alt key - must use WM_SYSKEYDOWN/UP because Alt doesn't fire WM_KEYDOWN
    case WM_SYSKEYDOWN: {
        if (wParam == VK_MENU) {
            g_state.altPressed = true;
        }
        return 0;  // Eat it to prevent system menu activation
    }

    case WM_SYSKEYUP: {
        if (wParam == VK_MENU) {
            g_state.altPressed = false;
        }
        return 0;
    }

    case WM_LBUTTONDOWN: {
        g_state.lmbPressed = true;
        double x = (double)LOWORD(lParam);
        double y = (double)HIWORD(lParam);
        OnMouseDown(g_state, x, y);
        SetCapture(hwnd);
        return 0;
    }
    case WM_LBUTTONUP: {
        g_state.lmbPressed = false;
        if (!g_state.mmbPressed && !g_state.rmbPressed) {
            g_state.dragging = false;
            ReleaseCapture();
        }
        return 0;
    }

    case WM_MBUTTONDOWN: {
        g_state.mmbPressed = true;
        double x = (double)LOWORD(lParam);
        double y = (double)HIWORD(lParam);
        OnMouseDown(g_state, x, y);
        SetCapture(hwnd);
        return 0;
    }
    case WM_MBUTTONUP: {
        g_state.mmbPressed = false;
        if (!g_state.lmbPressed && !g_state.rmbPressed) {
            g_state.dragging = false;
            ReleaseCapture();
        }
        return 0;
    }

    case WM_RBUTTONDOWN: {
        g_state.rmbPressed = true;
        double x = (double)LOWORD(lParam);
        double y = (double)HIWORD(lParam);
        OnMouseDown(g_state, x, y);
        SetCapture(hwnd);
        return 0;
    }
    case WM_RBUTTONUP: {
        g_state.rmbPressed = false;
        if (!g_state.lmbPressed && !g_state.mmbPressed) {
            g_state.dragging = false;
            ReleaseCapture();
        }
        return 0;
    }

    case WM_MOUSEMOVE: {
        double x = (double)LOWORD(lParam);
        double y = (double)HIWORD(lParam);
        OnMouseDrag(g_state, x, y);
        return 0;
    }

    case WM_DROPFILES: {
        HDROP hDrop = (HDROP)wParam;
        wchar_t wpath[MAX_PATH] = {};
        if (DragQueryFileW(hDrop, 0, wpath, MAX_PATH)) {
            int len = WideCharToMultiByte(CP_UTF8, 0, wpath, -1, nullptr, 0, nullptr, nullptr);
            std::string utf8Path(len - 1, '\0');
            WideCharToMultiByte(CP_UTF8, 0, wpath, -1, &utf8Path[0], len, nullptr, nullptr);
            LoadAndReplaceScene(hwnd, utf8Path);
        }
        DragFinish(hDrop);
        return 0;
    }
    }

    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

// --- Entry Point ---

int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int nCmdShow) {
    SetProcessDPIAware();

    // Allocate console for debug output
    AllocConsole();
    FILE* dummy;
    freopen_s(&dummy, "CONOUT$", "w", stdout);
    freopen_s(&dummy, "CONOUT$", "w", stderr);

    // Parse command line
    int argc;
    LPWSTR* argv = CommandLineToArgvW(GetCommandLineW(), &argc);

    if (argc < 2) {
        std::cout << "No model specified, using default scene.\n";
        CreateDefaultScene(g_state.scene);
    } else {
        // Convert wide string path to UTF-8
        int pathLen = WideCharToMultiByte(CP_UTF8, 0, argv[1], -1, nullptr, 0, nullptr, nullptr);
        std::string path(pathLen - 1, '\0');
        WideCharToMultiByte(CP_UTF8, 0, argv[1], -1, &path[0], pathLen, nullptr, nullptr);

        std::cout << "Loading " << path << "...\n";

        if (!LoadModel(path, g_state.scene)) {
            std::cerr << "Failed to load model.\n";
            LocalFree(argv);
            return 1;
        }
    }
    LocalFree(argv);

    if (sceneTriangleCount(g_state.scene) == 0) {
        std::cerr << "No triangles in scene.\n";
        return 1;
    }

    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << sceneTriangleCount(g_state.scene) << " triangles.\n";

    // Initialize sun direction and accumulation buffer
    g_state.sunDirection = Vec3(1, 1, -0.5f).normalize();
    g_state.pixels.resize(g_state.width * g_state.height);
    g_state.accumBuffer.resize((size_t)g_state.width * g_state.height * 3, 0.0f);
    FitToScene(g_state);

    // Register window class
    WNDCLASSEXW wc = {};
    wc.cbSize        = sizeof(wc);
    wc.style         = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = hInstance;
    wc.hCursor       = LoadCursor(nullptr, IDC_ARROW);
    wc.lpszClassName = L"LightRTViewer";
    RegisterClassExW(&wc);

    // Create window
    RECT rc = { 0, 0, (LONG)g_state.width, (LONG)g_state.height };
    AdjustWindowRectEx(&rc, WS_OVERLAPPEDWINDOW, FALSE, 0);

    HWND hwnd = CreateWindowExW(
        0, L"LightRTViewer", L"LightRT Viewer (Win32)",
        WS_OVERLAPPEDWINDOW,
        CW_USEDEFAULT, CW_USEDEFAULT,
        rc.right - rc.left, rc.bottom - rc.top,
        nullptr, nullptr, hInstance, nullptr);

    ShowWindow(hwnd, nCmdShow);
    UpdateWindow(hwnd);
    DragAcceptFiles(hwnd, TRUE);

    UpdateBitmapInfo();

    QueryPerformanceFrequency(&g_perfFreq);
    QueryPerformanceCounter(&g_lastTime);

    LARGE_INTEGER fpsTimer = g_lastTime;
    int fpsFrameCount = 0;

    std::cout << "Controls: Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, Alt+RMB/Ctrl+Shift+LMB/Tab+LMB Dolly\n";
    std::cout << "          F: Fit, S: Shadow, +: Font 2x, O: Open File, Drag&Drop: Load file\n";

    // Main loop
    while (g_running) {
        MSG msg;
        while (PeekMessageW(&msg, nullptr, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) {
                g_running = false;
                break;
            }
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
        if (!g_running) break;

        // Timing
        LARGE_INTEGER now;
        QueryPerformanceCounter(&now);
        float dt = (float)(now.QuadPart - g_lastTime.QuadPart) / (float)g_perfFreq.QuadPart;
        g_lastTime = now;

        // FPS counter
        fpsFrameCount++;
        float fpsElapsed = (float)(now.QuadPart - fpsTimer.QuadPart) / (float)g_perfFreq.QuadPart;
        if (fpsElapsed >= 1.0f) {
            g_state.fps = fpsFrameCount / fpsElapsed;
            fpsFrameCount = 0;
            fpsTimer = now;
        }

        // Process input
        if (ProcessInput(g_state, dt)) {
            g_running = false;
            break;
        }

        // Render
        RenderFrame(g_state);

        // Blit to window via GDI
        HDC hdc = GetDC(hwnd);
        SetDIBitsToDevice(hdc,
            0, 0, g_state.width, g_state.height,
            0, 0, 0, g_state.height,
            g_state.pixels.data(), &g_bmi, DIB_RGB_COLORS);
        ReleaseDC(hwnd, hdc);
    }

    DestroyWindow(hwnd);
    return 0;
}
