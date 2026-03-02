#!/usr/bin/env node
const fs = require('fs-extra');
const path = require('path');
const axios = require('axios');
const css = require('css');
const { fontSplit } = require('cn-font-split');
const CleanCSS = require('clean-css');
const chalk = require('chalk').default;
const pLimit = require('p-limit').default;

const CONFIG_FILE = 'fontkit.config.json';
const DIST_DIR = path.resolve(process.cwd(), 'dist');
const FONTS_DIR = path.join(DIST_DIR, 'fonts');
const OFFLINE_FONTS_DIR = path.resolve(process.cwd(), 'offline_fonts');
const CUSTOM_CSS_PATH = path.resolve(__dirname, 'custom.css');
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

async function downloadFile(url, dest, print_log = true, referer = '', maxRetries = 3) {
    const filename = path.basename(dest);
    
    for (let attempt = 1; attempt <= maxRetries; attempt++) {
        try {
            const config = {
                responseType: 'arraybuffer',
                headers: {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
                },
                timeout: 30000 // 30 second timeout
            };
            if (referer) {
                config.headers['Referer'] = referer;
            }
            
            const response = await axios.get(url, config);
            await fs.outputFile(dest, response.data);
            
            if (attempt === 1 && print_log === true) {
                console.log(`${chalk.green('✓')} ${chalk.cyan(filename)} (${response.data.length} bytes)`);
            }
            return true;
            
        } catch (error) {
            if (attempt === maxRetries) {
                console.error(`${chalk.red('✗')} ${chalk.cyan(filename)} - ${error.message}`);
                if (error.response) {
                    console.error(`  Status: ${error.response.status}`);
                }
                return false;
            } else {
                console.log(`${chalk.yellow('⚠')} ${chalk.cyan(filename)} - Retry ${attempt}/${maxRetries}`);
                await new Promise(resolve => setTimeout(resolve, 1000 * attempt)); // Exponential backoff
            }
        }
    }
}

// Strategy: Robust JS Emulation
async function extractFontsFromJS(kitId) {
    console.log(`[Method: JS Emulation] Attempting Kit ${kitId}...`);
    const jsUrl = `https://use.typekit.net/${kitId}.js`;
    let jsContent = '';

    // 1. Fetch JS
    // Try to find local file first for speed/offline dev
    // Try to find local file first for speed/offline dev
    const localJsPath = path.resolve(process.cwd(), `${kitId}.js`);
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
    console.log(`${chalk.blue('---')} Processing Typekit Fonts ${chalk.blue('---')}`);

    let cssOutput = '/* Typekit Fonts */\n';

    for (const kitId of kits) {
        console.log(`\n${chalk.blue('Kit:')} ${chalk.bold(kitId)}`);

        const fonts = await extractFontsFromJS(kitId);

        if (fonts.length === 0) {
            console.error(`${chalk.red('✗')} Failed to get fonts for kit ${kitId}`);
            continue;
        }

        console.log(`${chalk.green('✓')} Found ${fonts.length} fonts`);

        let kitCss = `/* Kit ${kitId} */\n`;

        for (const font of fonts) {
            const localFilename = font.filename || path.basename(font.fullUrl.split('?')[0]);
            const localPath = path.join(FONTS_DIR, 'typekit', localFilename);
            const relativePath = `./fonts/typekit/${localFilename}`;

            const success = await downloadFile(font.fullUrl, localPath, true, 'https://use.typekit.net/');

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


async function processGoogle(googleFonts, isLegacy = false) {
    if (!googleFonts || googleFonts.length === 0) return '';
    const mode = isLegacy ? chalk.yellow('(Legacy)') : chalk.blue('(Modern)');
    console.log(`${chalk.blue('---')} Processing Google Fonts ${mode} ${chalk.blue('---')}`);

    let fullCss = '';
    const fontsDir = isLegacy ? path.join(FONTS_DIR, 'legacy') : FONTS_DIR;
    const limit = pLimit(4); // Limit concurrent downloads

    for (const fontRequest of googleFonts) {
        const url = `https://fonts.googleapis.com/css2?family=${fontRequest}&display=swap`;
        console.log(`${chalk.blue('Font:')} ${chalk.bold(fontRequest)}`);

        try {
            const userAgent = isLegacy 
                ? 'Mozilla/5.0 (Windows NT 6.1; Trident/7.0; rv:11.0) like Gecko'
                : 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36';
            
            const response = await axios.get(url, {
                headers: { 
                    'User-Agent': userAgent,
                    'Referer': 'https://fonts.googleapis.com/'
                }
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

                                // Generate a safe filename for legacy mode
                                const filename = isLegacy 
                                    ? `font_${Math.random().toString(36).substr(2, 9)}.woff`
                                    : path.basename(fullUrl);
                                
                                const localPath = path.join(fontsDir, 'google', filename);
                                const relativePath = isLegacy 
                                    ? `./fonts/legacy/google/${filename}`
                                    : `./fonts/google/${filename}`;

                                cssContent = cssContent.split(fullUrl).join(relativePath);
                                downloadPromises.push(limit(() => downloadFile(fullUrl, localPath, false)));
                            }
                        }
                    }
                }
            }
            await Promise.all(downloadPromises);
            fullCss += cssContent + '\n';

        } catch (e) {
            console.error(`${chalk.red('✗')} Failed Google Font ${fontRequest}: ${e.message}`);
        }
    }

    return `/* Google Fonts ${isLegacy ? '(Legacy)' : ''} */\n${fullCss}`;
}

async function processOffline(offlineFonts, isLegacy = false) {
    if (!offlineFonts || offlineFonts.length === 0) return '';
    const mode = isLegacy ? chalk.yellow('(Legacy)') : chalk.blue('(Modern)');
    console.log(`${chalk.blue('---')} Processing Offline Fonts ${mode} ${chalk.blue('---')}`);

    if (!await fs.pathExists(OFFLINE_FONTS_DIR)) {
        console.log('No offline fonts directory found.');
        return '';
    }

    let finalCss = '';
    const fontsDir = isLegacy ? path.join(FONTS_DIR, 'legacy') : FONTS_DIR;

    for (const fontCfg of offlineFonts) {
        const file = fontCfg.file;
        const inputPath = path.join(OFFLINE_FONTS_DIR, file);

        if (!await fs.pathExists(inputPath)) {
            console.error(`${chalk.red('✗')} Offline font file not found: ${inputPath}`);
            continue;
        }

        if (isLegacy) {
            // Legacy mode: Convert to WOFF format and place directly in legacy folder
            const fontName = path.parse(file).name;
            const ext = path.extname(file).toLowerCase();
            let outputFilename;
            let formatType;
            
            if (ext === '.ttf' || ext === '.otf') {
                outputFilename = `${fontName}.woff`;
                formatType = 'woff';
            } else {
                // For other formats, keep original extension
                outputFilename = file;
                formatType = ext.substring(1); // Remove the dot
            }
            
            const outputPath = path.join(fontsDir, outputFilename);
            
            console.log(`${chalk.blue('Font:')} ${chalk.bold(file)}`);
            
            // For now, just copy the file as-is since we don't have a conversion tool
            // In a real implementation, you would use a tool like fontforge or opentype.js
            // to convert TTF/OTF to WOFF
            await fs.copy(inputPath, outputPath);
            
            const relativePath = isLegacy 
                ? `./fonts/legacy/${outputFilename}`
                : `./fonts/offline/${outputFilename}`;

            finalCss += `/* Offline Font: ${file} (Legacy) */\n@font-face {\n  font-family: '${fontCfg.family}';\n  font-style: ${fontCfg.style || 'normal'};\n  font-weight: ${fontCfg.weight};\n  font-display: swap;\n  src: url('${relativePath}') format('${formatType}');\n}\n\n`;
        } else {
            // Normal mode: Use fontsplit
            const fontName = path.parse(file).name;
            const outputDir = path.join(fontsDir, 'offline', fontName);

            console.log(`${chalk.blue('Font:')} ${chalk.bold(file)}`);
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
    }
    return finalCss;
}

async function main() {
    console.log(`${chalk.blue('🚀')} Starting font build process...`);
    
    await loadConfig();
    await fs.ensureDir(DIST_DIR);
    await fs.emptyDir(DIST_DIR);

    // Regular fonts processing
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
        console.error(`${chalk.red('✗')} Minification errors:`, minified.errors);
    }

    const fontsMinCssPath = path.join(DIST_DIR, 'fonts.min.css');
    await fs.outputFile(fontsMinCssPath, minified.styles);

    // Legacy fonts processing
    if (config.legacy) {
        console.log(`\n${chalk.yellow('🔧')} Processing Legacy Fonts`);
        
        const legacyGoogleCss = await processGoogle(config.legacy.google || [], true);
        const legacyOfflineCss = await processOffline(config.legacy.offline || [], true);
        
        const legacyFullCss = `${legacyGoogleCss}\n${legacyOfflineCss}`;

        // Output unminified
        const legacyCssPath = path.join(DIST_DIR, 'fonts.legacy.css');
        await fs.outputFile(legacyCssPath, legacyFullCss);

        // Output minified
        const legacyMinified = new CleanCSS({
            level: 2,
            format: false
        }).minify(legacyFullCss);

        if (legacyMinified.errors.length > 0) {
            console.error(`${chalk.red('✗')} Legacy Minification errors:`, legacyMinified.errors);
        }

        const legacyMinCssPath = path.join(DIST_DIR, 'fonts.legacy.min.css');
        await fs.outputFile(legacyMinCssPath, legacyMinified.styles);
        
        console.log(`${chalk.green('✓')} Legacy CSS: ${legacyCssPath}`);
        console.log(`${chalk.green('✓')} Legacy Min: ${legacyMinCssPath}`);
    }

    
    console.log(`\n${chalk.green('🎉')} Build complete!`);
    console.log(`${chalk.green('✓')} CSS: ${fontsCssPath}`);
    console.log(`${chalk.green('✓')} Min: ${fontsMinCssPath}`);
}

main();
