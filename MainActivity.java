package com.sebastian.obbtool;

import android.app.Activity;
import android.app.AlertDialog;
import android.content.ContentResolver;
import android.content.Context;
import android.content.Intent;
import android.graphics.Bitmap;
import android.graphics.Color;
import android.net.Uri;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.util.Base64;
import android.view.Gravity;
import android.view.View;
import android.view.inputmethod.InputMethodManager;
import android.widget.ArrayAdapter;
import android.widget.Button;
import android.widget.EditText;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ListView;
import android.widget.TextView;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class MainActivity extends Activity {

    private static final int PICK_OBB = 100;
    private static final int CREATE_OBB = 101;
    private static final int PICK_PNG = 102;
    private static final int CREATE_PNG = 103;
    private static final int EXTRACT_BASE = 1000;

    private final ExecutorService executor =
    Executors.newSingleThreadExecutor();

    private final Handler mainHandler =
    new Handler(Looper.getMainLooper());

    private TextView status;
    private EditText search;
    private ListView entryList;
    private Button saveButton;

    private ArrayAdapter<String> adapter;

    private final ArrayList<Integer> visibleIndexes =
    new ArrayList<Integer>();

    private Object python;
    private Object bridge;

    private File sourceObb;

    private int currentEntry = -1;
    private int currentTexture = -1;

    private AlertDialog textureDialog;

    private ImageView previewImage;
    private TextView previewInfo;

    private Uri pendingUri;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        setContentView(R.layout.activity_main);

        status = findViewById(R.id.status);
        search = findViewById(R.id.search);
        entryList = findViewById(R.id.entryList);
        saveButton = findViewById(R.id.saveButton);

        Button openButton = findViewById(R.id.openButton);

        adapter = new ArrayAdapter<String>(
            this,
            android.R.layout.simple_list_item_1,
            new ArrayList<String>()
        );

        entryList.setAdapter(adapter);

        /*
         * Start Python.
         */
        try {
            Class<?> pythonClass =
                Class.forName("com.chaquo.python.Python");
            python = pythonClass
                .getMethod("getInstance")
                .invoke(null);
            bridge = python.getClass()
                .getMethod("getModule", String.class)
                .invoke(python, "bridge");

            status.setText("Ready");
        } catch (Throwable e) {
            status.setText("Python bridge unavailable");

            new AlertDialog.Builder(this)
                .setTitle("Python Error")
                .setMessage(
                "Hindi ma-load ang Chaquopy Python bridge.\n\n"
                + e.toString()
            )
                .setPositiveButton("OK", null)
                .show();
        }

        /*
         * OPEN OBB
         */
        openButton.setOnClickListener(
            new View.OnClickListener() {
                @Override
                public void onClick(View v) {
                    pickObb();
                }
            }
        );

        /*
         * SAVE OBB
         */
        saveButton.setOnClickListener(
            new View.OnClickListener() {
                @Override
                public void onClick(View v) {
                    pickSaveObb();
                }
            }
        );

        saveButton.setEnabled(false);

        /*
         * ENTRY CLICK
         */
        entryList.setOnItemClickListener(
            new android.widget.AdapterView.OnItemClickListener() {
                @Override
                public void onItemClick(
                    android.widget.AdapterView<?> parent,
                    View view,
                    int position,
                    long id) {

                    if (position < visibleIndexes.size()) {
                        int index =
                            visibleIndexes.get(position);

                        openEntry(index);
                    }
                }
            }
        );

        /*
         * SEARCH
         *
         * TextWatcher is kept permanently attached.
         * This fixes the "keyboard works once only" issue.
         */
        search.addTextChangedListener(
            new android.text.TextWatcher() {

                @Override
                public void beforeTextChanged(
                    CharSequence s,
                    int start,
                    int count,
                    int after) {
                }

                @Override
                public void onTextChanged(
                    CharSequence s,
                    int start,
                    int before,
                    int count) {

                    if (sourceObb != null) {
                        filterEntries(s.toString());
                    }
                }

                @Override
                public void afterTextChanged(
                    android.text.Editable s) {
                }
            }
        );

        /*
         * Force keyboard every time search receives focus.
         */
        search.setOnFocusChangeListener(
            new View.OnFocusChangeListener() {

                @Override
                public void onFocusChange(
                    View v,
                    boolean hasFocus) {

                    if (hasFocus) {

                        search.postDelayed(
                            new Runnable() {

                                @Override
                                public void run() {

                                    InputMethodManager imm =
                                        (InputMethodManager)
                                        getSystemService(
                                        Context.INPUT_METHOD_SERVICE
                                    );

                                    if (imm != null) {
                                        imm.showSoftInput(
                                            search,
                                            InputMethodManager.SHOW_IMPLICIT
                                        );
                                    }
                                }
                            },
                            150
                        );
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * FILE PICKERS
     * ============================================================
     */

    private void pickObb() {

        Intent intent =
            new Intent(Intent.ACTION_OPEN_DOCUMENT);

        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("*/*");

        intent.addFlags(
            Intent.FLAG_GRANT_READ_URI_PERMISSION
            | Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION
        );

        startActivityForResult(intent, PICK_OBB);
    }

    private void pickSaveObb() {

        if (sourceObb == null) {
            toast("Open an OBB first.");
            return;
        }

        String name = sourceObb.getName();

        if (name.toLowerCase().endsWith(".obb")) {
            name = name.substring(
                0,
                name.length() - 4
            );
        }

        name = name + "_edited.obb";

        Intent intent =
            new Intent(Intent.ACTION_CREATE_DOCUMENT);

        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("application/octet-stream");
        intent.putExtra(Intent.EXTRA_TITLE, name);

        startActivityForResult(
            intent,
            CREATE_OBB
        );
    }

    private void pickPng() {

        Intent intent =
            new Intent(Intent.ACTION_OPEN_DOCUMENT);

        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("image/png");

        intent.addFlags(
            Intent.FLAG_GRANT_READ_URI_PERMISSION
            | Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION
        );

        startActivityForResult(
            intent,
            PICK_PNG
        );
    }

    private void createPngDestination() {

        if (currentTexture < 0) {
            toast("No texture selected.");
            return;
        }

        Intent intent =
            new Intent(Intent.ACTION_CREATE_DOCUMENT);

        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("image/png");

        intent.putExtra(
            Intent.EXTRA_TITLE,
            "texture_" + currentTexture + ".png"
        );

        startActivityForResult(
            intent,
            CREATE_PNG
        );
    }

    /*
     * ============================================================
     * ACTIVITY RESULT
     * ============================================================
     */

    @Override
    protected void onActivityResult(
        int requestCode,
        int resultCode,
        Intent data) {

        super.onActivityResult(
            requestCode,
            resultCode,
            data
        );

        if (resultCode != RESULT_OK || data == null) {
            return;
        }

        Uri uri = data.getData();

        if (uri == null) {
            return;
        }

        if (requestCode == PICK_OBB) {

            try {
                getContentResolver()
                    .takePersistableUriPermission(
                    uri,
                    Intent.FLAG_GRANT_READ_URI_PERMISSION
                );
            } catch (Throwable ignored) {
            }

            openObbFromUri(uri);
            return;
        }

        if (requestCode == CREATE_OBB) {

            pendingUri = uri;
            saveObbToUri(uri);
            return;
        }

        if (requestCode == PICK_PNG) {

            importPngFromUri(uri);
            return;
        }

        if (requestCode == CREATE_PNG) {

            pendingUri = uri;
            exportTextureToUri(uri);
            return;
        }

        if (requestCode >= EXTRACT_BASE) {

            int entry =
                requestCode - EXTRACT_BASE;

            extractEntryToUri(
                entry,
                uri
            );
        }
    }

    /*
     * ============================================================
     * OPEN OBB
     * ============================================================
     */

    private void openObbFromUri(final Uri uri) {

        setBusy("Copying OBB...");

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        File dst =
                            new File(
                            getCacheDir(),
                            "source.obb"
                        );

                        copyUriToFile(
                            uri,
                            dst
                        );

                        String json =
                            callPy(
                            "open_obb",
                            dst.getAbsolutePath(),
                            getCacheDir()
                            .getAbsolutePath()
                        );

                        JSONObject result =
                            new JSONObject(json);

                        sourceObb = dst;

                        final JSONArray rows =
                            result.getJSONArray("rows");

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    rebuildEntryList(
                                        rows,
                                        ""
                                    );

                                    status.setText(
                                        "Loaded "
                                        + rows.length()
                                        + " OBB entries"
                                    );

                                    saveButton.setEnabled(
                                        false
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * SEARCH
     * ============================================================
     */

    private void filterEntries(
        final String query) {

        if (sourceObb == null) {
            return;
        }

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        String json =
                            callPy(
                            "obb_rows",
                            query
                        );

                        final JSONArray rows =
                            new JSONArray(json);

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    rebuildEntryList(
                                        rows,
                                        query
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    private void rebuildEntryList(
        JSONArray rows,
        String query) {

        adapter.clear();
        visibleIndexes.clear();

        try {

            for (int i = 0;
                 i < rows.length();
            i++) {

                JSONArray row =
                    rows.getJSONArray(i);

                int index =
                    row.optInt(0);

                String name =
                    row.optString(1);

                String hash =
                    row.optString(2);

                String type =
                    row.optString(3);

                long size =
                    row.optLong(4);

                boolean staged =
                    row.optBoolean(7, false);

                boolean editable =
                    row.optBoolean(8, false);

                StringBuilder label =
                    new StringBuilder();

                label.append(index);
                label.append("  ");
                label.append(name);

                label.append("\n");

                label.append(type);
                label.append("  ");
                label.append(size);
                label.append(" bytes");

                if (hash != null
                    && hash.length() > 0) {

                    label.append("\nHash: ");
                    label.append(hash);
                }

                if (editable) {

                    if (staged) {
                        label.append(
                            "  • EDITED"
                        );
                    } else {
                        label.append(
                            "  • EDITABLE"
                        );
                    }
                }

                adapter.add(
                    label.toString()
                );

                visibleIndexes.add(index);
            }

        } catch (Throwable e) {

            toast(
                "List error: "
                + e.getMessage()
            );
        }

        adapter.notifyDataSetChanged();

        status.setText(
            rows.length()
            + " matching entries"
        );
    }

    /*
     * ============================================================
     * ENTRY
     * ============================================================
     */

    private void openEntry(
        final int index) {

        currentEntry = index;

        setBusy(
            "Opening entry "
            + index
            + "..."
        );

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        String json =
                            callPy(
                            "open_entry",
                            index
                        );

                        final JSONObject obj =
                            new JSONObject(json);

                        final JSONArray textures =
                            obj.optJSONArray(
                            "textures"
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    showEntryDialog(
                                        obj,
                                        textures
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    private void showEntryDialog(
        final JSONObject obj,
        final JSONArray textures) {

        LinearLayout root =
            new LinearLayout(this);

        root.setOrientation(
            LinearLayout.VERTICAL
        );

        root.setPadding(
            24,
            12,
            24,
            12
        );

        TextView info =
            new TextView(this);

        info.setTextSize(16);

        String name =
            obj.optString(
            "name",
            "IFF"
        );

        int textureCount =
            textures == null
            ? 0
            : textures.length();

        info.setText(
            "Entry "
            + currentEntry
            + "\n"
            + name
            + "\n\nTextures: "
            + textureCount
        );

        root.addView(info);

        Button strings =
            new Button(this);

        strings.setText(
            "STRINGS PREVIEW"
        );

        root.addView(strings);

        Button raw =
            new Button(this);

        raw.setText(
            "EXTRACT RAW ENTRY"
        );

        root.addView(raw);

        ListView textureList =
            new ListView(this);

        ArrayList<String> names =
            new ArrayList<String>();

        if (textures != null) {

            for (int i = 0;
                 i < textures.length();
            i++) {

                JSONObject t =
                    textures.optJSONObject(i);

                if (t == null) {
                    continue;
                }

                StringBuilder text =
                    new StringBuilder();

                text.append(
                    "Texture "
                    + t.optInt("number")
                );

                text.append(
                    " • "
                    + t.optString(
                        "format"
                    )
                );

                text.append(
                    "\n"
                    + t.optInt("width")
                    + " x "
                    + t.optInt("height")
                );

                text.append(
                    "\nPayload: "
                    + t.optLong(
                        "payload_size"
                    )
                    + " bytes"
                );

                text.append(
                    "\n"
                    + t.optString(
                        "location"
                    )
                );

                names.add(
                    text.toString()
                );
            }
        }

        textureList.setAdapter(
            new ArrayAdapter<String>(
                this,
                android.R.layout.simple_list_item_1,
                names
            )
        );

        root.addView(
            textureList,
            new LinearLayout.LayoutParams(
                -1,
                0,
                1.0f
            )
        );

        final AlertDialog dialog =
            new AlertDialog.Builder(this)
            .setTitle(name)
            .setView(root)
            .setNegativeButton(
            "CLOSE",
            null
        )
            .create();

        textureList.setOnItemClickListener(
            new android.widget.AdapterView.OnItemClickListener() {

                @Override
                public void onItemClick(
                    android.widget.AdapterView<?> parent,
                    View view,
                    int position,
                    long id) {

                    if (textures == null) {
                        return;
                    }

                    JSONObject t =
                        textures.optJSONObject(
                        position
                    );

                    if (t != null) {

                        showTexture(
                            t.optInt(
                                "number"
                            )
                        );
                    }
                }
            }
        );

        strings.setOnClickListener(
            new View.OnClickListener() {

                @Override
                public void onClick(View v) {
                    showStrings();
                }
            }
        );

        raw.setOnClickListener(
            new View.OnClickListener() {

                @Override
                public void onClick(View v) {
                    extractCurrentEntry();
                }
            }
        );

        dialog.show();

        status.setText(
            "Opened " + name
        );
    }

    /*
     * ============================================================
     * TEXTURE PREVIEW
     * ============================================================
     */

    private void showTexture(
        int textureNumber) {

        currentTexture =
            textureNumber;

        LinearLayout root =
            new LinearLayout(this);

        root.setOrientation(
            LinearLayout.VERTICAL
        );

        root.setPadding(
            8,
            8,
            8,
            8
        );

        previewImage =
            new ImageView(this);

        previewImage.setBackgroundColor(
            Color.BLACK
        );

        previewImage.setAdjustViewBounds(
            true
        );

        previewImage.setScaleType(
            ImageView.ScaleType.FIT_CENTER
        );

        root.addView(
            previewImage,
            new LinearLayout.LayoutParams(
                -1,
                0,
                1.0f
            )
        );

        previewInfo =
            new TextView(this);

        previewInfo.setTextColor(
            Color.WHITE
        );

        previewInfo.setPadding(
            8,
            8,
            8,
            8
        );

        root.addView(
            previewInfo
        );

        LinearLayout buttons =
            new LinearLayout(this);

        buttons.setOrientation(
            LinearLayout.HORIZONTAL
        );

        Button repair =
            new Button(this);

        repair.setText(
            "AUTO FIX ETC2"
        );

        Button export =
            new Button(this);

        export.setText(
            "EXPORT PNG"
        );

        Button importButton =
            new Button(this);

        importButton.setText(
            "IMPORT PNG"
        );

        buttons.addView(
            repair,
            new LinearLayout.LayoutParams(
                0,
                -2,
                1.0f
            )
        );

        buttons.addView(
            export,
            new LinearLayout.LayoutParams(
                0,
                -2,
                1.0f
            )
        );

        buttons.addView(
            importButton,
            new LinearLayout.LayoutParams(
                0,
                -2,
                1.0f
            )
        );

        root.addView(buttons);

        textureDialog =
            new AlertDialog.Builder(this)
            .setTitle(
            "Texture "
            + textureNumber
        )
            .setView(root)
            .setNegativeButton(
            "CLOSE",
            null
        )
            .create();

        repair.setOnClickListener(
            new View.OnClickListener() {

                @Override
                public void onClick(View v) {
                    loadTexture(true);
                }
            }
        );

        export.setOnClickListener(
            new View.OnClickListener() {

                @Override
                public void onClick(View v) {
                    createPngDestination();
                }
            }
        );

        importButton.setOnClickListener(
            new View.OnClickListener() {

                @Override
                public void onClick(View v) {
                    pickPng();
                }
            }
        );

        textureDialog.show();

        loadTexture(false);
    }

    /*
     * ============================================================
     * DECODE ETC2
     * ============================================================
     */

    private void loadTexture(
        final boolean autoRepair) {

        if (currentEntry < 0
            || currentTexture < 0) {

            return;
        }

        if (bridge == null) {
            toast(
                "Python bridge is not available."
            );
            return;
        }

        if (previewImage == null) {
            return;
        }

        setBusy(
            autoRepair
            ? "Repairing ETC2..."
            : "Decoding ETC2..."
        );

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        String json =
                            callPy(
                            "decode_texture_base64",
                            currentTexture,
                            autoRepair
                        );

                        final JSONObject obj =
                            new JSONObject(json);

                        String encoded =
                            obj.optString(
                            "rgba_b64"
                        );

                        if (encoded.length() == 0) {
                            throw new Exception(
                                "Decoder returned no RGBA data."
                            );
                        }

                        byte[] rgba =
                            Base64.decode(
                            encoded,
                            Base64.DEFAULT
                        );

                        final int width =
                            obj.optInt(
                            "width"
                        );

                        final int height =
                            obj.optInt(
                            "height"
                        );

                        if (width <= 0
                            || height <= 0) {

                            throw new Exception(
                                "Invalid texture size: "
                                + width
                                + "x"
                                + height
                            );
                        }

                        long expected =
                            (long) width
                            * (long) height
                            * 4L;

                        if (rgba.length < expected) {

                            throw new Exception(
                                "RGBA buffer is too small.\n"
                                + "Expected: "
                                + expected
                                + "\nReceived: "
                                + rgba.length
                            );
                        }

                        /*
                         * Bitmap creation can use a lot of RAM.
                         * Keep the operation on the worker thread.
                         */
                        final Bitmap bitmap =
                            Bitmap.createBitmap(
                            width,
                            height,
                            Bitmap.Config.ARGB_8888
                        );

                        int[] pixels =
                            new int[
                            width * height
                            ];

                        int p = 0;

                        for (int i = 0;
                             i < pixels.length;
                        i++) {

                            int r =
                                rgba[p++] & 255;

                            int g =
                                rgba[p++] & 255;

                            int b =
                                rgba[p++] & 255;

                            int a =
                                rgba[p++] & 255;

                            pixels[i] =
                                Color.argb(
                                a,
                                r,
                                g,
                                b
                            );
                        }

                        bitmap.setPixels(
                            pixels,
                            0,
                            width,
                            0,
                            0,
                            width,
                            height
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    if (previewImage != null) {

                                        previewImage
                                            .setImageBitmap(
                                            bitmap
                                        );
                                    }

                                    if (previewInfo != null) {

                                        StringBuilder info =
                                            new StringBuilder();

                                        info.append(
                                            width
                                            + "x"
                                            + height
                                        );

                                        info.append(
                                            " • "
                                            + obj.optString(
                                                "format"
                                            )
                                        );

                                        info.append(
                                            "\nETC2 layout: "
                                            + obj.optString(
                                                "layout"
                                            )
                                        );

                                        info.append(
                                            "\nScore: "
                                            + obj.optString(
                                                "score"
                                            )
                                        );

                                        if (autoRepair) {

                                            info.append(
                                                "\nAUTO REPAIR: DONE"
                                            );
                                        }

                                        previewInfo.setText(
                                            info.toString()
                                        );
                                    }

                                    status.setText(
                                        "Texture decoded"
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * PNG EXPORT
     * ============================================================
     */

    private void exportTextureToUri(
        final Uri uri) {

        if (currentTexture < 0) {
            return;
        }

        setBusy("Exporting PNG...");

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        File out =
                            new File(
                            getCacheDir(),
                            "texture_export.png"
                        );

                        callPy(
                            "extract_texture_png",
                            currentTexture,
                            out.getAbsolutePath(),
                            true
                        );

                        copyFileToUri(
                            out,
                            uri
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {
                                    status.setText(
                                        "PNG exported"
                                    );

                                    toast(
                                        "PNG exported"
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * PNG IMPORT
     * ============================================================
     */

    private void importPngFromUri(
        final Uri uri) {

        if (currentTexture < 0) {
            toast("Select a texture first.");
            return;
        }

        setBusy("Importing PNG...");

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        File png =
                            new File(
                            getCacheDir(),
                            "texture_import.png"
                        );

                        copyUriToFile(
                            uri,
                            png
                        );

                        callPy(
                            "import_texture_png",
                            currentTexture,
                            png.getAbsolutePath()
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    saveButton
                                        .setEnabled(
                                        true
                                    );

                                    status.setText(
                                        "PNG imported"
                                    );

                                    toast(
                                        "PNG imported and staged."
                                    );

                                    loadTexture(false);
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * STRINGS
     * ============================================================
     */

    private void showStrings() {

        setBusy(
            "Scanning printable strings..."
        );

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        final String text =
                            callPy(
                            "strings_preview",
                            131072
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    EditText output =
                                        new EditText(
                                        MainActivity.this
                                    );

                                    output.setText(
                                        text
                                    );

                                    output.setTextIsSelectable(
                                        true
                                    );

                                    output.setGravity(
                                        Gravity.TOP
                                    );

                                    output.setSingleLine(
                                        false
                                    );

                                    new AlertDialog.Builder(
                                        MainActivity.this
                                    )
                                        .setTitle(
                                        "Strings Preview"
                                    )
                                        .setView(
                                        output
                                    )
                                        .setPositiveButton(
                                        "ASCII REPLACE",
                                        new android.content.DialogInterface.OnClickListener() {

                                            @Override
                                            public void onClick(
                                                android.content.DialogInterface dialog,
                                                int which) {

                                                showAsciiReplace();
                                            }
                                        }
                                    )
                                        .setNegativeButton(
                                        "CLOSE",
                                        null
                                    )
                                        .show();
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * ASCII SEARCH / REPLACE
     * ============================================================
     */

    private void showAsciiReplace() {

        LinearLayout box =
            new LinearLayout(this);

        box.setOrientation(
            LinearLayout.VERTICAL
        );

        box.setPadding(
            24,
            8,
            24,
            8
        );

        final EditText find =
            new EditText(this);

        find.setHint(
            "Find ASCII"
        );

        final EditText replace =
            new EditText(this);

        replace.setHint(
            "Replace"
        );

        box.addView(find);
        box.addView(replace);

        final AlertDialog dialog =
            new AlertDialog.Builder(this)
            .setTitle(
            "Search / Replace ASCII"
        )
            .setView(box)
            .setPositiveButton(
            "REPLACE",
            null
        )
            .setNegativeButton(
            "CANCEL",
            null
        )
            .create();

        dialog.setOnShowListener(
            new android.content.DialogInterface.OnShowListener() {

                @Override
                public void onShow(
                    android.content.DialogInterface d) {

                    Button button =
                        dialog.getButton(
                        AlertDialog.BUTTON_POSITIVE
                    );

                    button.setOnClickListener(
                        new View.OnClickListener() {

                            @Override
                            public void onClick(View v) {

                                String from =
                                    find.getText()
                                    .toString();

                                String to =
                                    replace.getText()
                                    .toString();

                                if (from.length() == 0) {

                                    find.setError(
                                        "Enter text to find."
                                    );

                                    return;
                                }

                                /*
                                 * UTF-8 byte length is what
                                 * matters, not Java characters.
                                 */
                                int fromBytes =
                                    from.getBytes(
                                    java.nio.charset.StandardCharsets.UTF_8
                                ).length;

                                int toBytes =
                                    to.getBytes(
                                    java.nio.charset.StandardCharsets.UTF_8
                                ).length;

                                if (fromBytes
                                    != toBytes) {

                                    replace.setError(
                                        "Replacement must have the same UTF-8 byte length."
                                    );

                                    toast(
                                        "Same byte length required."
                                    );

                                    return;
                                }

                                dialog.dismiss();

                                replaceAscii(
                                    from,
                                    to
                                );
                            }
                        }
                    );
                }
            }
        );

        dialog.show();
    }

    private void replaceAscii(
        final String from,
        final String to) {

        setBusy(
            "Replacing ASCII..."
        );

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        callPy(
                            "replace_ascii",
                            from,
                            to
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    saveButton
                                        .setEnabled(
                                        true
                                    );

                                    status.setText(
                                        "ASCII replacement staged"
                                    );

                                    toast(
                                        "ASCII replacement staged."
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * EXTRACT ENTRY
     * ============================================================
     */

    private void extractCurrentEntry() {

        if (currentEntry < 0) {
            return;
        }

        Intent intent =
            new Intent(
            Intent.ACTION_CREATE_DOCUMENT
        );

        intent.addCategory(
            Intent.CATEGORY_OPENABLE
        );

        intent.setType(
            "application/octet-stream"
        );

        intent.putExtra(
            Intent.EXTRA_TITLE,
            "entry_"
            + currentEntry
            + ".bin"
        );

        startActivityForResult(
            intent,
            EXTRACT_BASE
            + currentEntry
        );
    }

    private void extractEntryToUri(
        final int entry,
        final Uri uri) {

        setBusy(
            "Extracting entry..."
        );

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        File out =
                            new File(
                            getCacheDir(),
                            "entry_"
                            + entry
                            + ".bin"
                        );

                        callPy(
                            "extract_entry",
                            entry,
                            out.getAbsolutePath()
                        );

                        copyFileToUri(
                            out,
                            uri
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    status.setText(
                                        "Entry extracted"
                                    );

                                    toast(
                                        "Entry extracted."
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * SAVE OBB
     * ============================================================
     */

    private void saveObbToUri(
        final Uri uri) {

        setBusy(
            "Rebuilding OBB..."
        );

        executor.execute(
            new Runnable() {

                @Override
                public void run() {

                    try {

                        File out =
                            new File(
                            getCacheDir(),
                            "edited.obb"
                        );

                        String report =
                            callPy(
                            "save_obb",
                            out.getAbsolutePath()
                        );

                        if (!out.exists()) {

                            throw new Exception(
                                "Python did not create edited.obb."
                            );
                        }

                        if (out.length() <= 0) {

                            throw new Exception(
                                "Generated OBB is empty."
                            );
                        }

                        copyFileToUri(
                            out,
                            uri
                        );

                        mainHandler.post(
                            new Runnable() {

                                @Override
                                public void run() {

                                    saveButton
                                        .setEnabled(
                                        false
                                    );

                                    status.setText(
                                        "OBB saved successfully"
                                    );

                                    toast(
                                        "OBB saved."
                                    );
                                }
                            }
                        );

                    } catch (Throwable e) {

                        showError(e);
                    }
                }
            }
        );
    }

    /*
     * ============================================================
     * PYTHON BRIDGE
     * ============================================================
     */

    private String callPy(
        String function,
        Object... args)
    throws Exception {

        if (bridge == null) {

            throw new Exception(
                "Python bridge is unavailable.\n\n"
                + "Make sure Chaquopy is configured."
            );
        }

        Object result =
            callPythonAttr(bridge, function, args);

        if (result == null) {

            throw new Exception(
                "Python function returned null: "
                + function
            );
        }

        Object converted =
            result.getClass()
                .getMethod("toJava", Class.class)
                .invoke(result, String.class);

        return (String) converted;
    }

    private Object callPythonAttr(
        Object module,
        String function,
        Object[] args
    ) throws Exception {

        Class<?> cls = module.getClass();

        for (java.lang.reflect.Method method : cls.getMethods()) {
            if (!method.getName().equals("callAttr")) {
                continue;
            }

            Class<?>[] types = method.getParameterTypes();
            if (types.length == 2
                && types[0] == String.class
                && types[1].isArray()) {

                return method.invoke(module, function, args);
            }
        }

        throw new NoSuchMethodException(
            "Chaquopy callAttr method not found"
        );
    }

    /*
     * ============================================================
     * UI HELPERS
     * ============================================================
     */

    private void setBusy(
        final String message) {

        mainHandler.post(
            new Runnable() {

                @Override
                public void run() {

                    if (status != null) {
                        status.setText(
                            message
                        );
                    }
                }
            }
        );
    }

    private void showError(
        Throwable throwable) {

        String message;

        if (throwable == null) {

            message =
                "Unknown error.";

        } else if (throwable.getMessage() != null) {

            message =
                throwable.getMessage();

        } else {

            message =
                throwable.toString();
        }

        final String finalMessage =
            message;

        mainHandler.post(
            new Runnable() {

                @Override
                public void run() {

                    new AlertDialog.Builder(
                        MainActivity.this
                    )
                        .setTitle(
                        "Personal OBB Tool"
                    )
                        .setMessage(
                        finalMessage
                    )
                        .setPositiveButton(
                        "OK",
                        null
                    )
                        .show();
                }
            }
        );
    }

    private void toast(
        final String message) {

        mainHandler.post(
            new Runnable() {

                @Override
                public void run() {

                    Toast.makeText(
                        MainActivity.this,
                        message,
                        Toast.LENGTH_LONG
                    ).show();
                }
            }
        );
    }

    /*
     * ============================================================
     * FILE I/O
     * ============================================================
     */

    private void copyUriToFile(
        Uri uri,
        File destination)
    throws Exception {

        ContentResolver resolver =
            getContentResolver();

        InputStream input =
            resolver.openInputStream(uri);

        if (input == null) {

            throw new Exception(
                "Cannot open selected file."
            );
        }

        FileOutputStream output =
            new FileOutputStream(
            destination
        );

        try {

            byte[] buffer =
                new byte[1024 * 1024];

            int count;

            while ((count =
                   input.read(buffer)) != -1) {

                output.write(
                    buffer,
                    0,
                    count
                );
            }

            output.flush();

        } finally {

            try {
                input.close();
            } catch (Throwable ignored) {
            }

            try {
                output.close();
            } catch (Throwable ignored) {
            }
        }
    }

    private void copyFileToUri(
        File source,
        Uri uri)
    throws Exception {

        ContentResolver resolver =
            getContentResolver();

        InputStream input =
            new FileInputStream(
            source
        );

        OutputStream output =
            resolver.openOutputStream(
            uri
        );

        if (output == null) {

            input.close();

            throw new Exception(
                "Cannot open destination."
            );
        }

        try {

            byte[] buffer =
                new byte[1024 * 1024];

            int count;

            while ((count =
                   input.read(buffer)) != -1) {

                output.write(
                    buffer,
                    0,
                    count
                );
            }

            output.flush();

        } finally {

            try {
                input.close();
            } catch (Throwable ignored) {
            }

            try {
                output.close();
            } catch (Throwable ignored) {
            }
        }
    }

    /*
     * ============================================================
     * BACK / DESTROY
     * ============================================================
     */

    @Override
    public void onBackPressed() {

        if (textureDialog != null
            && textureDialog.isShowing()) {

            textureDialog.dismiss();
            return;
        }

        super.onBackPressed();
    }

    @Override
    protected void onDestroy() {

        try {
            executor.shutdownNow();
        } catch (Throwable ignored) {
        }

        if (previewImage != null) {

            previewImage.setImageDrawable(
                null
            );
        }

        previewImage = null;
        previewInfo = null;

        super.onDestroy();
    }
}
