@echo off
chcp 65001 >nul
cd /d "%~dp0"
where py >nul 2>nul
if %errorlevel%==0 (
    py -3 flowchart_studio.py %*
) else (
    python flowchart_studio.py %*
)
if errorlevel 1 pause
