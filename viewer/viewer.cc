// Thin GLFW + Vulkan shell — all platform-agnostic logic lives in common/viewer_common.h

#include "vk_loader.h"
#include <GLFW/glfw3.h>

#include "common/viewer_common.h"

#include <iostream>
#include <chrono>
#include <thread>

using namespace lightrt_viewer;

// --- Global State ---
static ViewerState g_state;

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
    bool framebufferResized = false;

    void Check(VkResult result, const char* msg) {
        if (result != VK_SUCCESS) {
            std::cerr << "Vulkan Error: " << msg << " (" << result << ")\n";
            exit(1);
        }
    }

    void Init(GLFWwindow* window, uint32_t w, uint32_t h) {
        width = w; height = h;
        LoadVulkan();

        VkApplicationInfo appInfo = {VK_STRUCTURE_TYPE_APPLICATION_INFO, nullptr, "Viewer", 1, "No Engine", 1, VK_API_VERSION_1_1};

        uint32_t glfwExtCount = 0;
        const char** glfwExts = glfwGetRequiredInstanceExtensions(&glfwExtCount);

        VkInstanceCreateInfo createInfo = {VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO};
        createInfo.pApplicationInfo = &appInfo;
        createInfo.enabledExtensionCount = glfwExtCount;
        createInfo.ppEnabledExtensionNames = glfwExts;

        Check(vkCreateInstance(&createInfo, nullptr, &instance), "Create Instance");
        LoadInstanceFunctions(instance);

        if (glfwCreateWindowSurface(instance, window, nullptr, &surface) != VK_SUCCESS) {
            std::cerr << "Failed to create window surface\n"; exit(1);
        }

        uint32_t count = 0;
        vkEnumeratePhysicalDevices(instance, &count, nullptr);
        std::vector<VkPhysicalDevice> devices(count);
        vkEnumeratePhysicalDevices(instance, &count, devices.data());
        physicalDevice = devices[0];

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

    uint32_t FindMemoryType(uint32_t typeBits, VkMemoryPropertyFlags properties) {
        VkPhysicalDeviceMemoryProperties memProps;
        vkGetPhysicalDeviceMemoryProperties(physicalDevice, &memProps);
        for (uint32_t i = 0; i < memProps.memoryTypeCount; i++) {
            if ((typeBits & (1 << i)) && (memProps.memoryTypes[i].propertyFlags & properties) == properties) {
                return i;
            }
        }
        return 0;
    }

    void RecreateSwapchain(uint32_t newWidth, uint32_t newHeight) {
        vkDeviceWaitIdle(device);

        vkUnmapMemory(device, stagingMemory);
        vkDestroyBuffer(device, stagingBuffer, nullptr);
        vkFreeMemory(device, stagingMemory, nullptr);

        VkSwapchainKHR oldSwapchain = swapchain;

        width = newWidth;
        height = newHeight;

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
        swapchainInfo.oldSwapchain = oldSwapchain;

        Check(vkCreateSwapchainKHR(device, &swapchainInfo, nullptr, &swapchain), "Recreate Swapchain");
        vkDestroySwapchainKHR(device, oldSwapchain, nullptr);

        uint32_t count = 0;
        vkGetSwapchainImagesKHR(device, swapchain, &count, nullptr);
        swapchainImages.resize(count);
        vkGetSwapchainImagesKHR(device, swapchain, &count, swapchainImages.data());

        VkBufferCreateInfo bufInfo = {VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO};
        bufInfo.size = width * height * 4;
        bufInfo.usage = VK_BUFFER_USAGE_TRANSFER_SRC_BIT;
        vkCreateBuffer(device, &bufInfo, nullptr, &stagingBuffer);

        VkMemoryRequirements memReq;
        vkGetBufferMemoryRequirements(device, stagingBuffer, &memReq);

        VkMemoryAllocateInfo memAlloc = {VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO};
        memAlloc.allocationSize = memReq.size;
        memAlloc.memoryTypeIndex = FindMemoryType(memReq.memoryTypeBits,
            VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT);
        vkAllocateMemory(device, &memAlloc, nullptr, &stagingMemory);
        vkBindBufferMemory(device, stagingBuffer, stagingMemory, 0);
        vkMapMemory(device, stagingMemory, 0, memReq.size, 0, &mappedMemory);
    }

    bool Present(const std::vector<uint32_t>& pixels) {
        vkWaitForFences(device, 1, &renderFence, VK_TRUE, UINT64_MAX);
        vkResetFences(device, 1, &renderFence);

        uint32_t imageIndex;
        VkResult res = vkAcquireNextImageKHR(device, swapchain, UINT64_MAX, imageAvailableSemaphore, VK_NULL_HANDLE, &imageIndex);
        if (res == VK_ERROR_OUT_OF_DATE_KHR) {
            VkSubmitInfo empty = {VK_STRUCTURE_TYPE_SUBMIT_INFO};
            vkQueueSubmit(queue, 1, &empty, renderFence);
            return false;
        }
        if (res != VK_SUCCESS && res != VK_SUBOPTIMAL_KHR) {
            VkSubmitInfo empty = {VK_STRUCTURE_TYPE_SUBMIT_INFO};
            vkQueueSubmit(queue, 1, &empty, renderFence);
            return false;
        }

        memcpy(mappedMemory, pixels.data(), width * height * sizeof(uint32_t));

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

        res = vkQueuePresentKHR(queue, &presentInfo);
        if (res == VK_ERROR_OUT_OF_DATE_KHR || res == VK_SUBOPTIMAL_KHR) {
            return false;
        }
        return true;
    }
};

// --- GLFW Callbacks ---

static void cursor_pos_callback(GLFWwindow*, double xpos, double ypos) {
    OnMouseDrag(g_state, xpos, ypos);
}

static void mouse_button_callback(GLFWwindow* window, int button, int action, int) {
    double x, y;
    glfwGetCursorPos(window, &x, &y);

    if (action == GLFW_PRESS) {
        if (button == GLFW_MOUSE_BUTTON_LEFT) {
            g_state.lmbPressed = true;
            OnMouseDown(g_state, x, y);
        } else if (button == GLFW_MOUSE_BUTTON_MIDDLE) {
            g_state.mmbPressed = true;
            OnMouseDown(g_state, x, y);
        } else if (button == GLFW_MOUSE_BUTTON_RIGHT) {
            g_state.rmbPressed = true;
            OnMouseDown(g_state, x, y);
        }
    } else if (action == GLFW_RELEASE) {
        if (button == GLFW_MOUSE_BUTTON_LEFT) g_state.lmbPressed = false;
        else if (button == GLFW_MOUSE_BUTTON_MIDDLE) g_state.mmbPressed = false;
        else if (button == GLFW_MOUSE_BUTTON_RIGHT) g_state.rmbPressed = false;

        if (!g_state.lmbPressed && !g_state.mmbPressed && !g_state.rmbPressed) {
            g_state.dragging = false;
        }
    }
}

static void framebuffer_size_callback(GLFWwindow* window, int, int) {
    VulkanContext* vk = reinterpret_cast<VulkanContext*>(glfwGetWindowUserPointer(window));
    if (vk) vk->framebufferResized = true;
}

// --- Main ---

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cout << "No model specified, using default scene.\n";
        CreateDefaultScene(g_state.scene);
    } else {
        std::string path = argv[1];
        std::cout << "Loading " << path << "...\n";

        if (!LoadModel(path, g_state.scene)) {
            std::cerr << "Failed to load model.\n";
            return 1;
        }
    }

    g_state.scene.build();

    if (g_state.scene.allTriangles.empty()) {
        std::cerr << "No triangles in scene.\n";
        return 1;
    }

    std::cout << "Scene: " << g_state.scene.meshes.size() << " meshes, "
              << g_state.scene.allTriangles.size() << " triangles.\n";

    // Initialize sun direction and accumulation buffer
    g_state.sunDirection = Vec3(1, 1, -0.5f).normalize();
    g_state.pixels.resize(g_state.width * g_state.height);
    g_state.accumBuffer.resize((size_t)g_state.width * g_state.height * 3, 0.0f);
    FitToScene(g_state);

    if (!glfwInit()) return 1;
    glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
    GLFWwindow* window = glfwCreateWindow(g_state.width, g_state.height, "LightRT Viewer", nullptr, nullptr);
    glfwSetCursorPosCallback(window, cursor_pos_callback);
    glfwSetMouseButtonCallback(window, mouse_button_callback);

    VulkanContext vk;
    vk.Init(window, g_state.width, g_state.height);
    glfwSetWindowUserPointer(window, &vk);
    glfwSetFramebufferSizeCallback(window, framebuffer_size_callback);

    auto lastTime = std::chrono::high_resolution_clock::now();

    std::cout << "Controls: Alt+LMB/Shift+LMB Orbit, Alt+MMB/Ctrl+LMB Pan, Alt+RMB/Ctrl+Shift+LMB Dolly\n";
    std::cout << "          F: Fit, S: Shadow\n";

    while (!glfwWindowShouldClose(window)) {
        glfwPollEvents();

        // Handle window resize
        {
            int fw, fh;
            glfwGetFramebufferSize(window, &fw, &fh);
            if (fw > 0 && fh > 0 && (vk.framebufferResized || (uint32_t)fw != g_state.width || (uint32_t)fh != g_state.height)) {
                ResizeFramebuffer(g_state, (uint32_t)fw, (uint32_t)fh);
                vk.RecreateSwapchain(g_state.width, g_state.height);
                vk.framebufferResized = false;
            }
            if (fw == 0 || fh == 0) {
                std::this_thread::sleep_for(std::chrono::milliseconds(10));
                continue;
            }
        }

        auto currentTime = std::chrono::high_resolution_clock::now();
        std::chrono::duration<float> dt = currentTime - lastTime;

        if (dt.count() >= 1.0f) {
            g_state.fps = g_state.frameCount / dt.count();
            g_state.frameCount = 0;
            lastTime = currentTime;
        }

        // Poll keys
        g_state.keys[KEY_F]      = glfwGetKey(window, GLFW_KEY_F) == GLFW_PRESS;
        g_state.keys[KEY_S]      = glfwGetKey(window, GLFW_KEY_S) == GLFW_PRESS;
        g_state.keys[KEY_ESCAPE] = glfwGetKey(window, GLFW_KEY_ESCAPE) == GLFW_PRESS;
        g_state.altPressed = glfwGetKey(window, GLFW_KEY_LEFT_ALT) == GLFW_PRESS ||
                             glfwGetKey(window, GLFW_KEY_RIGHT_ALT) == GLFW_PRESS;
        g_state.shiftPressed = glfwGetKey(window, GLFW_KEY_LEFT_SHIFT) == GLFW_PRESS ||
                               glfwGetKey(window, GLFW_KEY_RIGHT_SHIFT) == GLFW_PRESS;
        g_state.ctrlPressed = glfwGetKey(window, GLFW_KEY_LEFT_CONTROL) == GLFW_PRESS ||
                              glfwGetKey(window, GLFW_KEY_RIGHT_CONTROL) == GLFW_PRESS;

        if (ProcessInput(g_state, 0.016f)) {
            glfwSetWindowShouldClose(window, true);
        }

        RenderFrame(g_state);

        if (!vk.Present(g_state.pixels)) {
            vk.framebufferResized = true;
        }
        g_state.frameCount++;
    }

    vkDeviceWaitIdle(vk.device);
    glfwDestroyWindow(window);
    glfwTerminate();

    return 0;
}
