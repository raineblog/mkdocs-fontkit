const fs = require('fs-extra');
const path = require('path');
const axios = require('axios');
const css = require('css');
const { fontSplit } = require('cn-font-split');
const CleanCSS = require('clean-css');

const CONFIG_FILE = 'fontkit.config.json';
const DIST_DIR = path.resolve(__dirname, '../dist');
const FONTS_DIR = path.join(DIST_DIR, 'fonts');
const OFFLINE_FONTS_DIR = path.resolve(__dirname, '../offline_fonts');
let config = {};

// --- Typekit JS Emulation Logic (Reverse Engineered) ---
// Ported from rur1fuq.js to generate 'unicode' and 'features' params locally

const H_CONST = [2449897292, 4218179547, 2675077685, 1031960064, 1478620578, 1386343184, 3194259988, 2656050674, 3012733295, 2193273665];

function G(a, b) {
    return (a & 65535) * b + (((a >>> 16) * b & 65535) << 16);
}

function Ba(a, b) {
    a = G(a & 4294967295, 3432918353);
    a = G(a << 15 | a >>> 17, 461845907);
    b = (b || 0) ^ a;
    b = G(b << 13 | b >>> 19, 5) + 3864292196;
    b ^= 4;
    b = G(b ^ b >>> 16, 2246822507);
    b = G(b ^ b >>> 13, 3266489909);
    return (b ^ b >>> 16) >>> 0;
}

function Ca(a, b) {
    b = b || 0;
    var c, d = a.length % 4,
        e = a.length - d;
    for (c = 0; c < e; c += 4) {
        var f = (a.charCodeAt(c) & 4294967295) << 0 | (a.charCodeAt(c + 1) & 4294967295) << 8 | (a.charCodeAt(c + 2) & 4294967295) << 16 | (a.charCodeAt(c + 3) & 4294967295) << 24;
        f = G(f, 3432918353);
        f = f << 15 | f >>> 17;
        f = G(f, 461845907);
        b ^= f;
        b = b << 13 | b >>> 19;
        b = G(b, 5) + 3864292196;
    }
    f = 0;
    switch (d) {
        case 3:
            f ^= (a.charCodeAt(c + 2) & 4294967295) << 16;
        case 2:
            f ^= (a.charCodeAt(c + 1) & 4294967295) << 8;
        case 1:
            f ^= (a.charCodeAt(c) & 4294967295) << 0;
            f = G(f, 3432918353);
            f = G(f << 15 | f >>> 17, 461845907);
            b ^= f;
    }
    b ^= a.length;
    b = G(b ^ b >>> 16, 2246822507);
    b = G(b ^ b >>> 13, 3266489909);
    return (b ^ b >>> 16) >>> 0;
}

class Da {
    constructor(a) {
        this.values = Array(Math.ceil(a / 32));
        this.size = a;
        for (let i = 0; i < this.values.length; i++) this.values[i] = 0;
    }
    set(a) {
        if (Math.floor(a / 32 + 1) > this.values.length) throw Error("Index is out of bounds.");
        var b = Math.floor(a / 32);
        this.values[b] |= 1 << a - 32 * b;
    }
    has(a) {
        if (Math.floor(a / 32 + 1) > this.values.length) throw Error("Index is out of bounds.");
        var b = Math.floor(a / 32);
        return !!(this.values[b] & 1 << a - 32 * b);
    }
}

class Ea {
    constructor(a, b) {
        this.size = a;
        this.g = b;
        this.data = new Da(a);
    }
    add(a) {
        if ("string" !== typeof a && "number" !== typeof a) throw Error("Value should be a string or number.");
        for (var b = "number" === typeof a, c = 0; c < this.g; c++) {
            this.data.set(b ? Ba(a, H_CONST[c]) % this.size : Ca(a, H_CONST[c]) % this.size);
        }
    }
}

function Fa(a) {
    // a is instance of Ea
    // Concatenate [size, g] and data.values
    var arr = [a.size, a.g].concat(a.data.values);
    var b = "";
    for (var c = 0; c < arr.length; c++) {
        var d = arr[c];
        // Big-endian 32-bit integer to bytes
        b += String.fromCharCode((d & 4278190080) >>> 24) +
            String.fromCharCode((d & 16711680) >>> 16) +
            String.fromCharCode((d & 65280) >>> 8) +
            String.fromCharCode((d & 255) >>> 0);
    }
    // Base64 encode
    var b64 = Buffer.from(b, 'binary').toString('base64');
    // URL safe replacement
    return b64.replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

function Ga(unicodeList) {
    if (unicodeList.length) {
        // Calculate Bloom filter parameters based on number of unicode points
        var b = Math.min(Math.ceil(Math.log(.01) * (unicodeList.length || 1) / Math.log(1 / Math.pow(2, Math.log(2)))), 9586);
        var c = new Ea(b, Math.max(Math.min(Math.round(Math.log(2) * b / (unicodeList.length || 1)), H_CONST.length), 1));
        unicodeList.forEach(function (d) {
            c.add(d);
        });
        return Fa(c);
    }
    return "AAAAAQAAAAEAAAAB";
}

// Unicode Range Parser (from P function)
function parseUnicodeRange(rangeStr) {
    var parts = (rangeStr || "").split(/\s*,\s*/);
    var result = [];
    for (var c = 0; c < parts.length; c++) {
        var d = /^(u\+([0-9a-f?]{1,6})(?:-([0-9a-f]{1,6}))?)$/i.exec(parts[c]);
        if (d) {
            if (-1 !== d[2].indexOf("?")) {
                var e = parseInt(d[2].replace(/\?/g, "0"), 16);
                var f = parseInt(d[2].replace(/\?/g, "f"), 16);
                for (; e <= f; e++) result.push(e);
            } else {
                var e = parseInt(d[2], 16);
                var g = d[3] ? parseInt(d[3], 16) : e;
                if (e !== g) {
                    for (; e <= g; e++) result.push(e);
                } else {
                    result.push(e);
                }
            }
        }
    }
    return result; // returning Array instead of Set for easier iteration
}

// --------------------------------------------------------

async function loadConfig() {
    if (await fs.pathExists(CONFIG_FILE)) {
        config = await fs.readJson(CONFIG_FILE);
    } else {
        // Default config template
        config = {
            adobe: [],
            google: [],
            offline: []
        };
        await fs.writeJson(CONFIG_FILE, config, { spaces: 2 });
    }
}

async function downloadFile(url, dest, referer = '') {
    try {
        const config = {
            responseType: 'arraybuffer',
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
            }
        };
        if (referer) {
            config.headers['Referer'] = referer;
        }
        const response = await axios.get(url, config);
        await fs.outputFile(dest, response.data);
        console.log(`Downloaded: ${url} -> ${dest}`);
        return true;
    } catch (error) {
        if (error.response && error.response.status === 404) {
            console.error(`Failed to download ${url}: 404 Not Found (Bad URL construction?)`);
        } else {
            console.error(`Failed to download ${url}: ${error.message}`);
        }
        return false;
    }
}

// Strategy: Robust JS Emulation
async function extractFontsFromJS(kitId) {
    console.log(`[Method: JS Emulation] Attempting Kit ${kitId}...`);
    const jsUrl = `https://use.typekit.net/${kitId}.js`;
    let jsContent = '';

    // 1. Fetch JS
    // Try to find local file first for speed/offline dev
    const localJsPath = path.resolve(__dirname, `../${kitId}.js`);
    if (await fs.pathExists(localJsPath)) {
        jsContent = await fs.readFile(localJsPath, 'utf8');
        console.log(`  Loaded local JS file: ${localJsPath}`);
    } else {
        try {
            const resp = await axios.get(jsUrl);
            jsContent = resp.data;
        } catch (e) {
            console.error(`  Failed to fetch JS: ${e.message}`);
            return [];
        }
    }

    // 2. Extract Config JSON
    // The file ends with: }({"a":"...","f":[...]}));
    const lastParenStart = jsContent.lastIndexOf('({"a":"');
    if (lastParenStart === -1) {
        console.error("  Could not find config object start.");
        return [];
    }

    let configStr = jsContent.substring(lastParenStart + 1);
    configStr = configStr.replace(/\)\);?\s*$/, '');

    let configObj = null;
    try {
        configObj = JSON.parse(configStr);
    } catch (e) {
        console.error("  JSON parse failed. Config string snippet: ", configStr.substring(0, 100));
        return [];
    }

    if (!configObj || !configObj.f) {
        console.error("  Invalid config object structure.");
        return [];
    }

    // 3. Generate Valid URLs
    const results = [];
    for (const font of configObj.f) {
        let templateUrl = font.source;
        templateUrl = templateUrl.replace('{format}', 'l');

        const unicodeRange = font.descriptors.unicodeRange;
        const unicodeList = parseUnicodeRange(unicodeRange);
        const unicodeParam = Ga(unicodeList);

        let featuresParam = "NONE";
        if (font.descriptors.featureSettings) {
            const fs = font.descriptors.featureSettings.trim();
            if (fs.indexOf("ALL") !== -1) featuresParam = "ALL";
            else {
                featuresParam = fs.replace(/['"]/g, '').trim();
            }
        }

        const vParam = "3";
        const baseUrl = templateUrl.split('{?')[0];
        const finalUrl = `${baseUrl}?unicode=${unicodeParam}&features=${featuresParam}&v=${vParam}`;

        const filename = `${kitId}-${font.id}.woff2`;

        results.push({
            fullUrl: finalUrl,
            filename: filename,
            family: font.family,
            descriptor: font.descriptors
        });
    }

    console.log(`[Method: JS Emulation] Generated ${results.length} URLs.`);
    return results;
}

// Orchestrator for Typekit (Static Analysis Only)
async function processTypekit(kits) {
    if (!kits || kits.length === 0) return '';
    console.log('--- Processing Typekit Fonts ---');

    let cssOutput = '/* Typekit Fonts */\n';

    for (const kitId of kits) {
        console.log(`\nProcessing Kit: ${kitId}`);

        const fonts = await extractFontsFromJS(kitId);

        if (fonts.length === 0) {
            console.error(`Failed to get fonts for kit ${kitId} using static analysis.`);
            continue;
        }

        console.log(`Successfully processed Kit ${kitId}, found ${fonts.length} fonts. Downloading...`);

        let kitCss = `/* Kit ${kitId} */\n`;

        for (const font of fonts) {
            const localFilename = font.filename || path.basename(font.fullUrl.split('?')[0]);
            const localPath = path.join(FONTS_DIR, 'typekit', localFilename);
            const relativePath = `./fonts/typekit/${localFilename}`;

            const success = await downloadFile(font.fullUrl, localPath, 'https://use.typekit.net/');

            if (success) {
                const desc = font.descriptor || {};
                kitCss += `
@font-face {
  font-family: '${font.family}';
  font-style: ${desc.style || 'normal'};
  font-weight: ${desc.weight || '400'};
  font-display: ${desc.display || 'auto'};
  src: url(${relativePath}) format('woff2');
  unicode-range: ${desc.unicodeRange || 'U+0-10FFFF'};
}
`;
            }
        }
        cssOutput += kitCss + '\n';
    }

    return cssOutput;
}


async function processGoogle(googleFonts) {
    if (!googleFonts || googleFonts.length === 0) return '';
    console.log('--- Processing Google Fonts ---');

    let fullCss = '';

    for (const fontRequest of googleFonts) {
        const url = `https://fonts.googleapis.com/css2?family=${fontRequest}&display=swap`;
        console.log(`Fetching Google CSS from: ${url}`);

        try {
            const response = await axios.get(url, {
                headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36' }
            });

            let cssContent = response.data;
            let cssObj = css.parse(cssContent);

            const rules = cssObj.stylesheet.rules;
            const downloadPromises = [];

            for (const rule of rules) {
                if (rule.type === 'font-face') {
                    for (const dec of rule.declarations) {
                        if (dec.property === 'src') {
                            const urlRegex = /url\(\s*(?:(["'])(.*?)\1|([^)]+))\s*\)/g;
                            let match;
                            while ((match = urlRegex.exec(dec.value)) !== null) {
                                const fullUrl = (match[2] || match[3] || '').trim();
                                if (!fullUrl) continue;

                                const filename = path.basename(fullUrl);
                                const localPath = path.join(FONTS_DIR, 'google', filename);
                                const relativePath = `./fonts/google/${filename}`;

                                cssContent = cssContent.split(fullUrl).join(relativePath);
                                downloadPromises.push(downloadFile(fullUrl, localPath));
                            }
                        }
                    }
                }
            }
            await Promise.all(downloadPromises);
            fullCss += cssContent + '\n';

        } catch (e) {
            console.error(`Failed Google Font ${fontRequest}: ${e.message}`);
        }
    }

    return `/* Google Fonts */\n${fullCss}`;
}

async function processOffline(offlineFonts) {
    if (!offlineFonts || offlineFonts.length === 0) return '';
    console.log('--- Processing Offline Fonts ---');

    if (!await fs.pathExists(OFFLINE_FONTS_DIR)) {
        console.log('No offline fonts directory found.');
        return '';
    }

    let finalCss = '';

    for (const fontCfg of offlineFonts) {
        const file = fontCfg.file;
        const inputPath = path.join(OFFLINE_FONTS_DIR, file);

        if (!await fs.pathExists(inputPath)) {
            console.error(`Offline font file not found: ${inputPath}`);
            continue;
        }

        const fontName = path.parse(file).name;
        const outputDir = path.join(FONTS_DIR, 'offline', fontName);

        console.log(`Splitting ${file}...`);
        const inputBuffer = await fs.readFile(inputPath);

        await fontSplit({
            input: inputBuffer,
            outDir: outputDir,
            css: {
                fontFamily: fontCfg.family,
                fontWeight: fontCfg.weight,
                fontStyle: fontCfg.style || 'normal'
            },
            renameOutputFont: '[hash:6].[ext]',
            silent: true
        });

        const outputFiles = await fs.readdir(outputDir);
        const cssFile = outputFiles.find(f => f.endsWith('.css'));

        if (cssFile) {
            let splitCss = await fs.readFile(path.join(outputDir, cssFile), 'utf8');
            const relativePrefix = `./fonts/offline/${fontName}/`;

            splitCss = splitCss.replace(/url\((['"]?)([^'")]+.woff2)(['"]?)\)/g, (match, q1, url, q3) => {
                const cleanUrl = path.basename(url);
                return `url(${q1}${relativePrefix}${cleanUrl}${q3})`;
            });

            finalCss += `/* Offline Font: ${file} */\n${splitCss}\n`;
        }
    }
    return finalCss;
}

async function main() {
    await loadConfig();
    await fs.ensureDir(DIST_DIR);
    await fs.emptyDir(DIST_DIR);

    const typekitCss = await processTypekit(config.typekit || config.adobe || []);
    const googleCss = await processGoogle(config.google);
    const offlineCss = await processOffline(config.offline);

    const fullCss = `${typekitCss}\n${googleCss}\n${offlineCss}`;

    // Output unminified
    const fontsCssPath = path.join(DIST_DIR, 'fonts.css');
    await fs.outputFile(fontsCssPath, fullCss);

    // Output minified
    const minified = new CleanCSS({
        level: 2,
        format: false // minified
    }).minify(fullCss);

    if (minified.errors.length > 0) {
        console.error('Minification errors:', minified.errors);
    }

    const fontsMinCssPath = path.join(DIST_DIR, 'fonts.min.css');
    await fs.outputFile(fontsMinCssPath, minified.styles);

    console.log('Build complete!');
    console.log(`- ${fontsCssPath}`);
    console.log(`- ${fontsMinCssPath}`);
}

main();
