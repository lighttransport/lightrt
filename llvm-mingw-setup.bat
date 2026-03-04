@echo off
setlocal enabledelayedexpansion

REM llvm-mingw-setup.bat - Configure CMake with llvm-mingw (clang++ + libc++), Ninja generator
REM Usage: llvm-mingw-setup.bat [build_dir] [build_type] [toolchain_path]
REM   build_dir      : Build output directory (default: build_llvm_mingw_x64 or build_llvm_mingw_arm64)
REM   build_type     : Release or Debug (default: Release)
REM   toolchain_path : llvm-mingw root (default: N:\local\llvm-mingw-20260224-ucrt-x86_64)

set BUILD_DIR=%~1

set BUILD_TYPE=%~2
if "%BUILD_TYPE%"=="" set BUILD_TYPE=Release

set "TOOLCHAIN=%~3"
if "%TOOLCHAIN%"=="" set "TOOLCHAIN=N:\local\llvm-mingw-20260224-ucrt-x86_64"

REM --- Detect host architecture ---
if "%PROCESSOR_ARCHITECTURE%"=="ARM64" (
    set ARCH_LABEL=arm64
    set TRIPLE=aarch64-w64-mingw32
) else (
    set ARCH_LABEL=x64
    set TRIPLE=x86_64-w64-mingw32
)
echo Host architecture: %ARCH_LABEL%

REM --- Set default build dir based on architecture ---
if "%BUILD_DIR%"=="" (
    if "%ARCH_LABEL%"=="arm64" (
        set BUILD_DIR=build_llvm_mingw_arm64
    ) else (
        set BUILD_DIR=build_llvm_mingw_x64
    )
)

REM --- Verify toolchain exists ---
if not exist "%TOOLCHAIN%\bin\clang++.exe" (
    echo ERROR: clang++.exe not found at %TOOLCHAIN%\bin\clang++.exe
    echo.
    echo Set toolchain path as 3rd argument or edit the default in this script.
    echo   Usage: llvm-mingw-setup.bat [build_dir] [build_type] [toolchain_path]
    exit /b 1
)

REM --- Prepend toolchain bin to PATH ---
set "PATH=%TOOLCHAIN%\bin;%PATH%"

REM --- Convert backslashes to forward slashes for CMake ---
set "TOOLCHAIN_CMAKE=%TOOLCHAIN:\=/%"

REM --- Verify required tools ---
where cmake.exe >nul 2>&1
if %ERRORLEVEL% neq 0 (
    echo ERROR: cmake.exe not found in PATH.
    exit /b 1
)

where ninja.exe >nul 2>&1
if %ERRORLEVEL% neq 0 (
    echo WARNING: ninja.exe not found in PATH.
    echo   Install via: winget install Ninja-build.Ninja
    exit /b 1
)

REM --- Show tool versions ---
echo.
echo Toolchain: %TOOLCHAIN%
echo Triple:    %TRIPLE%
echo.
echo Tools:
for /f "delims=" %%i in ('where clang++.exe') do echo   clang++.exe: %%i
for /f "delims=" %%i in ('where cmake.exe') do echo   cmake.exe:   %%i
for /f "delims=" %%i in ('where ninja.exe') do echo   ninja.exe:   %%i
echo.
"%TOOLCHAIN%\bin\clang++.exe" --version 2>&1 | findstr /i "clang version"
echo.

REM --- Configure CMake ---
echo Configuring CMake...
echo   Generator:  Ninja
echo   Build type: %BUILD_TYPE%
echo   Build dir:  %BUILD_DIR%
echo   Stdlib:     libc++
echo.

cmake -G Ninja -S . -B "%BUILD_DIR%" ^
    -DCMAKE_BUILD_TYPE=%BUILD_TYPE% ^
    -DCMAKE_C_COMPILER="%TOOLCHAIN_CMAKE%/bin/%TRIPLE%-clang.exe" ^
    -DCMAKE_CXX_COMPILER="%TOOLCHAIN_CMAKE%/bin/%TRIPLE%-clang++.exe" ^
    -DCMAKE_RC_COMPILER="%TOOLCHAIN_CMAKE%/bin/%TRIPLE%-windres.exe" ^
    -DCMAKE_AR="%TOOLCHAIN_CMAKE%/bin/llvm-ar.exe" ^
    -DCMAKE_RANLIB="%TOOLCHAIN_CMAKE%/bin/llvm-ranlib.exe" ^
    -DCMAKE_CXX_FLAGS="-stdlib=libc++"

if %ERRORLEVEL% neq 0 (
    echo.
    echo ERROR: CMake configuration failed.
    exit /b 1
)

echo.
echo Configuration successful!
echo.
echo To build:
echo   cmake --build %BUILD_DIR%
echo.
echo To build with verbose output:
echo   cmake --build %BUILD_DIR% -- -v
echo.

endlocal
