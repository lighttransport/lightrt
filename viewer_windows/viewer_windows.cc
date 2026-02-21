// Pure Win32 + GDI viewer — no GLFW, no Vulkan, no external deps beyond lightrt

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <shellapi.h>

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
        case 'W':      g_state.keys[KEY_W] = true; break;
        case 'A':      g_state.keys[KEY_A] = true; break;
        case 'S':      g_state.keys[KEY_S] = true; break;
        case 'D':      g_state.keys[KEY_D] = true; break;
        case 'F':      g_state.keys[KEY_F] = true; break;
        case VK_ESCAPE: g_state.keys[KEY_ESCAPE] = true; break;
        }
        return 0;
    }

    case WM_KEYUP: {
        switch (wParam) {
        case 'W':      g_state.keys[KEY_W] = false; break;
        case 'A':      g_state.keys[KEY_A] = false; break;
        case 'S':      g_state.keys[KEY_S] = false; break;
        case 'D':      g_state.keys[KEY_D] = false; break;
        case 'F':      g_state.keys[KEY_F] = false; break;
        case VK_ESCAPE: g_state.keys[KEY_ESCAPE] = false; break;
        }
        return 0;
    }

    case WM_LBUTTONDOWN: {
        bool captured = OnMouseButtonToggle(g_state);
        if (captured) {
            SetCapture(hwnd);
            ShowCursor(FALSE);
            // Center cursor
            RECT rc;
            GetClientRect(hwnd, &rc);
            POINT center = { (rc.right - rc.left) / 2, (rc.bottom - rc.top) / 2 };
            ClientToScreen(hwnd, &center);
            SetCursorPos(center.x, center.y);
        } else {
            ReleaseCapture();
            ShowCursor(TRUE);
        }
        return 0;
    }

    case WM_MOUSEMOVE: {
        if (g_state.mouseCaptured) {
            // Get current cursor position in screen coords
            POINT pt;
            GetCursorPos(&pt);

            // Get window center in screen coords
            RECT rc;
            GetClientRect(hwnd, &rc);
            POINT center = { (rc.right - rc.left) / 2, (rc.bottom - rc.top) / 2 };
            POINT screenCenter = center;
            ClientToScreen(hwnd, &screenCenter);

            // Calculate delta from center
            double dx = (double)(pt.x - screenCenter.x);
            double dy = (double)(pt.y - screenCenter.y);

            if (dx != 0.0 || dy != 0.0) {
                // Feed absolute-style coords: accumulate from center
                OnMouseMove(g_state, center.x + dx, center.y + dy);
                // Reset mouse position state to center for next frame
                g_state.lastX = (double)center.x;
                g_state.lastY = (double)center.y;
                g_state.firstMouse = false;
                // Re-center the cursor
                SetCursorPos(screenCenter.x, screenCenter.y);
            }
        }
        return 0;
    }
    }

    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

// --- Entry Point ---

int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int nCmdShow) {
    SetProcessDPIAware();

    // Parse command line
    int argc;
    LPWSTR* argv = CommandLineToArgvW(GetCommandLineW(), &argc);

    if (argc < 2) {
        MessageBoxW(nullptr, L"Usage: viewer_windows <model.obj/gltf/glb>", L"LightRT Viewer", MB_OK | MB_ICONERROR);
        LocalFree(argv);
        return 1;
    }

    // Convert wide string path to UTF-8
    int pathLen = WideCharToMultiByte(CP_UTF8, 0, argv[1], -1, nullptr, 0, nullptr, nullptr);
    std::string path(pathLen - 1, '\0');
    WideCharToMultiByte(CP_UTF8, 0, argv[1], -1, &path[0], pathLen, nullptr, nullptr);
    LocalFree(argv);

    // Allocate console for debug output
    AllocConsole();
    FILE* dummy;
    freopen_s(&dummy, "CONOUT$", "w", stdout);
    freopen_s(&dummy, "CONOUT$", "w", stderr);

    std::cout << "Loading " << path << "...\n";

    if (!LoadModel(path, g_state.mesh) || g_state.mesh.triangles.empty()) {
        std::cerr << "Failed to load model or empty.\n";
        return 1;
    }

    std::cout << "Building BVH for " << g_state.mesh.triangles.size() << " triangles...\n";
    lightrt::BVHBuildConfig config;
    g_state.mesh.bvh.build(g_state.mesh.triangles, config);
    std::cout << "BVH Built.\n";

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

    g_state.pixels.resize(g_state.width * g_state.height);
    UpdateBitmapInfo();

    QueryPerformanceFrequency(&g_perfFreq);
    QueryPerformanceCounter(&g_lastTime);

    LARGE_INTEGER fpsTimer = g_lastTime;
    int fpsFrameCount = 0;

    std::cout << "Controls: WASD + Mouse (Click to capture/release), F: Toggle render mode\n";

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
