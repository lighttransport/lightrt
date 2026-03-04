@echo off
setlocal enabledelayedexpansion

REM vcbuild.bat - Build with VS2022 environment
REM Usage: vcbuild.bat [build_dir] [target]
REM   build_dir : Build directory (default: build_vs2022_x64 or build_vs2022_arm64)
REM   target    : Build target (default: all)

set BUILD_DIR=%~1
set TARGET=%~2

REM --- Detect host architecture ---
if "%PROCESSOR_ARCHITECTURE%"=="ARM64" (
    set VCVARS_ARCH=arm64
    set ARCH_LABEL=arm64
) else (
    set VCVARS_ARCH=x64
    set ARCH_LABEL=x64
)

if "%BUILD_DIR%"=="" (
    if "%ARCH_LABEL%"=="arm64" (
        set BUILD_DIR=build_vs2022_arm64
    ) else (
        set BUILD_DIR=build_vs2022_x64
    )
)

REM --- Ensure MSVC environment ---
where cl.exe >nul 2>&1
if %ERRORLEVEL% neq 0 (
    set VS_EDITIONS=Enterprise Professional Community BuildTools Preview
    for %%e in (!VS_EDITIONS!) do (
        set "CANDIDATE=C:\Program Files\Microsoft Visual Studio\2022\%%e\VC\Auxiliary\Build\vcvarsall.bat"
        if exist "!CANDIDATE!" (
            call "!CANDIDATE!" %VCVARS_ARCH% >nul
            goto :do_build
        )
    )
    echo ERROR: Could not find VS2022. Run from Developer Command Prompt.
    exit /b 1
)

:do_build
if not exist "%BUILD_DIR%\build.ninja" (
    echo ERROR: %BUILD_DIR% not configured. Run vcsetup.bat first.
    exit /b 1
)

echo Building %BUILD_DIR%...
if "%TARGET%"=="" (
    cmake --build "%BUILD_DIR%"
) else (
    cmake --build "%BUILD_DIR%" --target "%TARGET%"
)

endlocal
