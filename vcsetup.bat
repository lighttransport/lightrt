@echo off
setlocal enabledelayedexpansion

REM vcsetup.bat - Configure CMake with VS2022, Ninja generator
REM Usage: vcsetup.bat [build_dir] [build_type]
REM   build_dir  : Build output directory (default: build_vs2022_x64 or build_vs2022_arm64)
REM   build_type : Release or Debug (default: Release)

set BUILD_DIR=%~1

set BUILD_TYPE=%~2
if "%BUILD_TYPE%"=="" set BUILD_TYPE=Release

REM --- Detect host architecture ---
if "%PROCESSOR_ARCHITECTURE%"=="ARM64" (
    set VCVARS_ARCH=arm64
    set ARCH_LABEL=arm64
) else (
    set VCVARS_ARCH=x64
    set ARCH_LABEL=x64
    if "%PROCESSOR_ARCHITECTURE%"=="x86" (
        if "%PROCESSOR_ARCHITEW6432%"=="" (
            set VCVARS_ARCH=x86
            set ARCH_LABEL=x64
        )
    )
)
echo Host architecture: %VCVARS_ARCH%

REM --- Set default build dir based on architecture ---
if "%BUILD_DIR%"=="" (
    if "%ARCH_LABEL%"=="arm64" (
        set BUILD_DIR=build_vs2022_arm64
    ) else (
        set BUILD_DIR=build_vs2022_x64
    )
)

REM --- Check if MSVC environment is already configured ---
where cl.exe >nul 2>&1
if %ERRORLEVEL% equ 0 (
    echo MSVC environment already configured.
    for /f "delims=" %%i in ('where cl.exe') do (
        echo   cl.exe: %%i
        goto :do_cmake
    )
)

echo MSVC environment not found. Searching for VS2022...

REM --- Search common VS2022 install paths ---
set VCVARSALL=
set VS_EDITIONS=Enterprise Professional Community BuildTools Preview

REM Check "Program Files" (standard for VS2022)
for %%e in (%VS_EDITIONS%) do (
    set "CANDIDATE=C:\Program Files\Microsoft Visual Studio\2022\%%e\VC\Auxiliary\Build\vcvarsall.bat"
    if exist "!CANDIDATE!" (
        set "VCVARSALL=!CANDIDATE!"
        echo Found VS2022 %%e
        goto :found_vcvars
    )
)

REM Check "Program Files (x86)" (uncommon for 2022, but possible for BuildTools)
for %%e in (%VS_EDITIONS%) do (
    set "CANDIDATE=C:\Program Files (x86)\Microsoft Visual Studio\2022\%%e\VC\Auxiliary\Build\vcvarsall.bat"
    if exist "!CANDIDATE!" (
        set "VCVARSALL=!CANDIDATE!"
        echo Found VS2022 %%e (x86 program files)
        goto :found_vcvars
    )
)

REM Check vswhere if available (handles custom install paths)
set "VSWHERE=C:\Program Files (x86)\Microsoft Visual Studio\Installer\vswhere.exe"
if exist "%VSWHERE%" (
    echo Using vswhere to locate VS2022...
    for /f "usebackq tokens=*" %%i in (`"%VSWHERE%" -version [17.0^,18.0^) -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath -latest`) do (
        set "CANDIDATE=%%i\VC\Auxiliary\Build\vcvarsall.bat"
        if exist "!CANDIDATE!" (
            set "VCVARSALL=!CANDIDATE!"
            echo Found VS2022 via vswhere: %%i
            goto :found_vcvars
        )
    )
)

echo ERROR: Could not find Visual Studio 2022.
echo.
echo Please install Visual Studio 2022 with C++ workload, or run this
echo script from a "Developer Command Prompt for VS 2022".
echo.
echo Checked locations:
for %%e in (%VS_EDITIONS%) do (
    echo   C:\Program Files\Microsoft Visual Studio\2022\%%e
)
exit /b 1

:found_vcvars
echo Calling: "%VCVARSALL%" %VCVARS_ARCH%
call "%VCVARSALL%" %VCVARS_ARCH%
if %ERRORLEVEL% neq 0 (
    echo ERROR: vcvarsall.bat failed.
    exit /b 1
)

REM Verify cl.exe is now available
where cl.exe >nul 2>&1
if %ERRORLEVEL% neq 0 (
    echo ERROR: cl.exe not found after running vcvarsall.bat.
    exit /b 1
)

:do_cmake
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
    echo   Or download from: https://github.com/nicolla/ninja/releases
    exit /b 1
)

REM --- Show tool versions ---
echo.
echo Tools:
for /f "delims=" %%i in ('where cl.exe') do echo   cl.exe:    %%i
for /f "delims=" %%i in ('where cmake.exe') do echo   cmake.exe: %%i
for /f "delims=" %%i in ('where ninja.exe') do echo   ninja.exe: %%i
echo.

REM --- Configure CMake ---
echo Configuring CMake...
echo   Generator:  Ninja
echo   Build type: %BUILD_TYPE%
echo   Build dir:  %BUILD_DIR%
echo.

cmake -G Ninja -S . -B "%BUILD_DIR%" ^
    -DCMAKE_BUILD_TYPE=%BUILD_TYPE% ^
    -DCMAKE_C_COMPILER=cl ^
    -DCMAKE_CXX_COMPILER=cl

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
