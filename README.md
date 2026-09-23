# GPS 信息叠加到视频画面

将运动轨迹（GPX）与骑行/跑步数据叠加到户外视频上，生成带实时数值面板（速度、距离、海拔、心率等）和轨迹地图的成片。

## 功能

- 导入 GPX 轨迹与视频，按时间戳对齐，把运动数据实时叠加到画面上
- 数值面板：速度 / 距离 / 海拔 / 心率 / 坡度 / 地理位置 等，可自定义字段与配色
- 全景轨迹图 + 可放大的当前位置轨迹图（深色底，透明度可调）
- 文字与图形固定 80% 透明度，仅背景底色透明度可调
- 支持拖放文件启动、批量调整时间偏移、速度实测校准
- 一键打包输出 MP4（内置 ffmpeg，无需额外安装）

## 使用

方式一（源码）：用仓库内 `GPSTool\python\python.exe` 运行 `GPSTool\gps_overlay_gui.py`，或直接双击 `GPSTool\启动工具.vbs`。

方式二（已打包 EXE）：到 [Releases](../../releases) 下载 `GPSTool_v1.1_win64.zip`，解压后双击 `GPSTool.exe` 即可。

## 目录结构

```
GPSTool/
├── gps_overlay_gui.py    # 界面与交互
├── gps_overlay_core.py   # 叠加渲染核心逻辑
├── GPSTool.spec          # PyInstaller 打包配置
├── 启动工具.vbs          # Windows 启动器（无黑框、支持拖放）
├── layouts.json          # 面板布局预设
├── README.md             # 工具说明
└── app.ico               # 程序图标
```

> 内置 Python 运行环境（`GPSTool/python/`）与 ffmpeg（`GPSTool/tools/`）体积较大，不纳入源码仓库，仅随 Release 资产分发。

## 版本

当前为 v1.1：数值面板 / 全景轨迹 / 放大轨迹 三组件基线，包含单位底部对齐、左栏顶/底空隙收缩等优化。
