#include "vk_loader.h"
#include <dlfcn.h>
#include <iostream>

// Definition of function pointers
PFN_vkCreateInstance vkCreateInstance = nullptr;
PFN_vkGetInstanceProcAddr vkGetInstanceProcAddr = nullptr;
PFN_vkEnumerateInstanceExtensionProperties vkEnumerateInstanceExtensionProperties = nullptr;

PFN_vkDestroyInstance vkDestroyInstance = nullptr;
PFN_vkCreateDevice vkCreateDevice = nullptr;
PFN_vkGetDeviceProcAddr vkGetDeviceProcAddr = nullptr;
PFN_vkEnumeratePhysicalDevices vkEnumeratePhysicalDevices = nullptr;
PFN_vkGetPhysicalDeviceProperties vkGetPhysicalDeviceProperties = nullptr;
PFN_vkGetPhysicalDeviceMemoryProperties vkGetPhysicalDeviceMemoryProperties = nullptr;
PFN_vkGetPhysicalDeviceQueueFamilyProperties vkGetPhysicalDeviceQueueFamilyProperties = nullptr;
PFN_vkGetPhysicalDeviceSurfaceSupportKHR vkGetPhysicalDeviceSurfaceSupportKHR = nullptr;
PFN_vkGetPhysicalDeviceSurfaceCapabilitiesKHR vkGetPhysicalDeviceSurfaceCapabilitiesKHR = nullptr;
PFN_vkGetPhysicalDeviceSurfaceFormatsKHR vkGetPhysicalDeviceSurfaceFormatsKHR = nullptr;
PFN_vkGetPhysicalDeviceSurfacePresentModesKHR vkGetPhysicalDeviceSurfacePresentModesKHR = nullptr;
PFN_vkDestroySurfaceKHR vkDestroySurfaceKHR = nullptr;

PFN_vkDestroyDevice vkDestroyDevice = nullptr;
PFN_vkGetDeviceQueue vkGetDeviceQueue = nullptr;
PFN_vkCreateSwapchainKHR vkCreateSwapchainKHR = nullptr;
PFN_vkDestroySwapchainKHR vkDestroySwapchainKHR = nullptr;
PFN_vkGetSwapchainImagesKHR vkGetSwapchainImagesKHR = nullptr;
PFN_vkAcquireNextImageKHR vkAcquireNextImageKHR = nullptr;
PFN_vkQueuePresentKHR vkQueuePresentKHR = nullptr;
PFN_vkCreateCommandPool vkCreateCommandPool = nullptr;
PFN_vkDestroyCommandPool vkDestroyCommandPool = nullptr;
PFN_vkAllocateCommandBuffers vkAllocateCommandBuffers = nullptr;
PFN_vkFreeCommandBuffers vkFreeCommandBuffers = nullptr;
PFN_vkBeginCommandBuffer vkBeginCommandBuffer = nullptr;
PFN_vkEndCommandBuffer vkEndCommandBuffer = nullptr;
PFN_vkQueueSubmit vkQueueSubmit = nullptr;
PFN_vkQueueWaitIdle vkQueueWaitIdle = nullptr;
PFN_vkDeviceWaitIdle vkDeviceWaitIdle = nullptr;
PFN_vkCreateSemaphore vkCreateSemaphore = nullptr;
PFN_vkDestroySemaphore vkDestroySemaphore = nullptr;
PFN_vkCreateFence vkCreateFence = nullptr;
PFN_vkDestroyFence vkDestroyFence = nullptr;
PFN_vkWaitForFences vkWaitForFences = nullptr;
PFN_vkResetFences vkResetFences = nullptr;
PFN_vkCreateBuffer vkCreateBuffer = nullptr;
PFN_vkDestroyBuffer vkDestroyBuffer = nullptr;
PFN_vkGetBufferMemoryRequirements vkGetBufferMemoryRequirements = nullptr;
PFN_vkAllocateMemory vkAllocateMemory = nullptr;
PFN_vkFreeMemory vkFreeMemory = nullptr;
PFN_vkBindBufferMemory vkBindBufferMemory = nullptr;
PFN_vkMapMemory vkMapMemory = nullptr;
PFN_vkUnmapMemory vkUnmapMemory = nullptr;
PFN_vkCmdPipelineBarrier vkCmdPipelineBarrier = nullptr;
PFN_vkCmdCopyBufferToImage vkCmdCopyBufferToImage = nullptr;

static void* libvulkan = nullptr;

template<typename T>
bool LoadFunc(T& func, const char* name) {
    func = reinterpret_cast<T>(dlsym(libvulkan, name));
    return func != nullptr;
}

template<typename T>
bool LoadInstanceFunc(VkInstance instance, T& func, const char* name) {
    func = reinterpret_cast<T>(vkGetInstanceProcAddr(instance, name));
    return func != nullptr;
}

template<typename T>
bool LoadDeviceFunc(VkDevice device, T& func, const char* name) {
    func = reinterpret_cast<T>(vkGetDeviceProcAddr(device, name));
    return func != nullptr;
}

bool LoadVulkan() {
    if (libvulkan) return true;
    
    libvulkan = dlopen("libvulkan.so.1", RTLD_NOW | RTLD_LOCAL);
    if (!libvulkan) {
        libvulkan = dlopen("libvulkan.so", RTLD_NOW | RTLD_LOCAL);
    }
    if (!libvulkan) {
        std::cerr << "Failed to load libvulkan.so\n";
        return false;
    }

    if (!LoadFunc(vkGetInstanceProcAddr, "vkGetInstanceProcAddr")) return false;
    if (!LoadFunc(vkCreateInstance, "vkCreateInstance")) return false;
    if (!LoadFunc(vkEnumerateInstanceExtensionProperties, "vkEnumerateInstanceExtensionProperties")) return false;

    // Load global functions that we need before instance creation (often same as instance funcs but loaded via dlsym or GetInstanceProcAddr with null)
    // Actually, best practice is to load everything else via GetInstanceProcAddr
    
    return true;
}

// Helper to load instance functions after instance creation
void LoadInstanceFunctions(VkInstance instance) {
    LoadInstanceFunc(instance, vkDestroyInstance, "vkDestroyInstance");
    LoadInstanceFunc(instance, vkCreateDevice, "vkCreateDevice");
    LoadInstanceFunc(instance, vkGetDeviceProcAddr, "vkGetDeviceProcAddr");
    LoadInstanceFunc(instance, vkEnumeratePhysicalDevices, "vkEnumeratePhysicalDevices");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceProperties, "vkGetPhysicalDeviceProperties");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceMemoryProperties, "vkGetPhysicalDeviceMemoryProperties");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceQueueFamilyProperties, "vkGetPhysicalDeviceQueueFamilyProperties");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceSurfaceSupportKHR, "vkGetPhysicalDeviceSurfaceSupportKHR");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceSurfaceCapabilitiesKHR, "vkGetPhysicalDeviceSurfaceCapabilitiesKHR");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceSurfaceFormatsKHR, "vkGetPhysicalDeviceSurfaceFormatsKHR");
    LoadInstanceFunc(instance, vkGetPhysicalDeviceSurfacePresentModesKHR, "vkGetPhysicalDeviceSurfacePresentModesKHR");
    LoadInstanceFunc(instance, vkDestroySurfaceKHR, "vkDestroySurfaceKHR");
}

void LoadDeviceFunctions(VkDevice device) {
    LoadDeviceFunc(device, vkDestroyDevice, "vkDestroyDevice");
    LoadDeviceFunc(device, vkGetDeviceQueue, "vkGetDeviceQueue");
    LoadDeviceFunc(device, vkCreateSwapchainKHR, "vkCreateSwapchainKHR");
    LoadDeviceFunc(device, vkDestroySwapchainKHR, "vkDestroySwapchainKHR");
    LoadDeviceFunc(device, vkGetSwapchainImagesKHR, "vkGetSwapchainImagesKHR");
    LoadDeviceFunc(device, vkAcquireNextImageKHR, "vkAcquireNextImageKHR");
    LoadDeviceFunc(device, vkQueuePresentKHR, "vkQueuePresentKHR");
    LoadDeviceFunc(device, vkCreateCommandPool, "vkCreateCommandPool");
    LoadDeviceFunc(device, vkDestroyCommandPool, "vkDestroyCommandPool");
    LoadDeviceFunc(device, vkAllocateCommandBuffers, "vkAllocateCommandBuffers");
    LoadDeviceFunc(device, vkFreeCommandBuffers, "vkFreeCommandBuffers");
    LoadDeviceFunc(device, vkBeginCommandBuffer, "vkBeginCommandBuffer");
    LoadDeviceFunc(device, vkEndCommandBuffer, "vkEndCommandBuffer");
    LoadDeviceFunc(device, vkQueueSubmit, "vkQueueSubmit");
    LoadDeviceFunc(device, vkQueueWaitIdle, "vkQueueWaitIdle");
    LoadDeviceFunc(device, vkDeviceWaitIdle, "vkDeviceWaitIdle");
    LoadDeviceFunc(device, vkCreateSemaphore, "vkCreateSemaphore");
    LoadDeviceFunc(device, vkDestroySemaphore, "vkDestroySemaphore");
    LoadDeviceFunc(device, vkCreateFence, "vkCreateFence");
    LoadDeviceFunc(device, vkDestroyFence, "vkDestroyFence");
    LoadDeviceFunc(device, vkWaitForFences, "vkWaitForFences");
    LoadDeviceFunc(device, vkResetFences, "vkResetFences");
    LoadDeviceFunc(device, vkCreateBuffer, "vkCreateBuffer");
    LoadDeviceFunc(device, vkDestroyBuffer, "vkDestroyBuffer");
    LoadDeviceFunc(device, vkGetBufferMemoryRequirements, "vkGetBufferMemoryRequirements");
    LoadDeviceFunc(device, vkAllocateMemory, "vkAllocateMemory");
    LoadDeviceFunc(device, vkFreeMemory, "vkFreeMemory");
    LoadDeviceFunc(device, vkBindBufferMemory, "vkBindBufferMemory");
    LoadDeviceFunc(device, vkMapMemory, "vkMapMemory");
    LoadDeviceFunc(device, vkUnmapMemory, "vkUnmapMemory");
    LoadDeviceFunc(device, vkCmdPipelineBarrier, "vkCmdPipelineBarrier");
    LoadDeviceFunc(device, vkCmdCopyBufferToImage, "vkCmdCopyBufferToImage");
}
