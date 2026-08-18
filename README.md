# Personal OBB Tool — Android 14 / Pydroid Engine Port

This project turns the working Pydroid Python engine into an Android APK using Chaquopy.

## Included

- NBA 2K20 OBB reader/writer using the existing custom 2K container parser
- Search by entry name/hash/type
- Lazy IFF opening
- IFF texture inventory
- ETC2 RGB / ETC2 RGBA8 pure-Python decoder
- ETC2 auto-layout repair with the existing candidate layouts
- RGB565 / RGBA4444 / RGBA8888 preview
- PNG export
- PNG import and IFF staging
- Strings preview
- Same-byte-length ASCII search/replace
- Raw entry extraction
- Verified OBB rebuild/save
- Android Storage Access Framework, so no broad storage permission is required
- ARM64-only packaging for modern Android phones

## Build

Recommended: Android Studio with a JDK compatible with the selected Android Gradle Plugin.

1. Open this folder as an Android Studio project.
2. Let Gradle sync.
3. Make sure Android SDK 35 is installed.
4. Make sure the Android SDK/NDK components requested by Gradle are installed.
5. Build > Make Project.
6. Run on an ARM64 Android 14 device.

The app uses Chaquopy 17 and Python 3.13. The Python code is under `app/src/main/python`.

## Important

The old Windows `.pyd` files were intentionally NOT copied into the Android project. Android cannot load those Windows binaries. ETC2 therefore uses the pure-Python decoder/repair code already present in the Pydroid version.

The Android UI is native Java. Tkinter is not used.

## ETC2 preview

For a texture which appears scrambled, open the texture and press `AUTO FIX ETC2`. The engine tests the supported block layouts and reports the selected layout/score. PNG export also uses the auto-repair path.

## AIDE

This project is designed first for a normal Gradle Android IDE such as Android Studio. AIDE support for modern external Gradle plugins can vary. If AIDE cannot sync the Chaquopy plugin, do not remove the plugin blindly: the Python engine depends on it. In that case build the same project in Android Studio, or a separate fully-native Java port would be required for AIDE-only builds.
