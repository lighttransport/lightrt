@echo off
setlocal

set SCRIPT_DIR=%~dp0
:: Remove trailing backslash
set SCRIPT_DIR=%SCRIPT_DIR:~0,-1%
set ROOT_DIR=%SCRIPT_DIR%\..
set DEPS_DIR=%ROOT_DIR%\deps
set TINYUSDZ_DIR=%DEPS_DIR%\tinyusdz
set BUILD_DIR=%SCRIPT_DIR%\build

:: Clone tinyusdz if not present
if not exist "%TINYUSDZ_DIR%\CMakeLists.txt" (
    echo Cloning tinyusdz ^(mtlx-nodegraph branch^)...
    mkdir "%DEPS_DIR%" 2>nul
    git clone --branch mtlx-nodegraph --depth 1 https://github.com/syoyo/tinyusdz.git "%TINYUSDZ_DIR%"
    if errorlevel 1 (
        echo ERROR: Failed to clone tinyusdz
        exit /b 1
    )
) else (
    echo tinyusdz already present at %TINYUSDZ_DIR%
)

:: Configure and build
echo.
echo Configuring with CMake...
mkdir "%BUILD_DIR%" 2>nul
cmake -S "%SCRIPT_DIR%" -B "%BUILD_DIR%" -G Ninja -DCMAKE_BUILD_TYPE=Release
if errorlevel 1 (
    echo ERROR: CMake configure failed
    exit /b 1
)

echo.
echo Building...
cmake --build "%BUILD_DIR%" --config Release
if errorlevel 1 (
    echo ERROR: Build failed
    exit /b 1
)

echo.
echo Build complete: %BUILD_DIR%\viewer_windows.exe
