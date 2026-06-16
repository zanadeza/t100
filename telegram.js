'use strict';

// ============================================================
// telegram.js — بوت تيليغرام مستقل كامل
// نفس ميزات بوت الواتساب بالكامل:
// ذكاء اصطناعي شامل، PDF، صور، صوت/TTS، ترجمة، VIP، كوتا، blacklist
// يعمل بشكل مستقل بدون أي اعتماد على بوت الواتساب
// التشغيل: node telegram.js
// ============================================================

require('dotenv').config();

const fs         = require('fs');
const path       = require('path');
const os         = require('os');
const crypto     = require('crypto');
const { execFile, execSync, spawnSync } = require('child_process');
const pdfParse   = require('pdf-parse');
const https      = require('https');
const http       = require('http');

// ============================================================
// CONFIG
// ============================================================
const TELEGRAM_TOKEN  = process.env.TELEGRAM_BOT_TOKEN;
const MISTRAL_API_KEY = process.env.MISTRAL_API_KEY;
const ADMIN_TG_ID     = parseInt(process.env.TELEGRAM_ADMIN_ID || '0', 10);
const BOT_NAME        = 'MedTerm';
const DATA_FILE       = './telegram_data.json';
const PDF_CACHE_DIR   = './pdf_cache_tg';
const TG_PORT         = process.env.TG_PORT || 8081;

if (!TELEGRAM_TOKEN) { console.error('❌ TELEGRAM_BOT_TOKEN غير موجود في .env'); process.exit(1); }
if (!MISTRAL_API_KEY) { console.error('❌ MISTRAL_API_KEY غير موجود في .env'); process.exit(1); }

// ============================================================
// LIMITS
// ============================================================
const DAILY_MSG_LIMIT        = 20;
const DAILY_IMG_LIMIT        = 5;
const DAILY_TTS_LIMIT        = 10;
const AUDIO_MAX_SECONDS_FREE = 5 * 60;
const AUDIO_MAX_SECONDS_VIP  = 15 * 60;
const MAX_HISTORY            = 12;
const API_TIMEOUT_MS         = 55_000;

// ============================================================
// DATA — محفوظة في telegram_data.json (منفصلة عن الواتساب)
// ============================================================
function loadData() {
    try {
        if (fs.existsSync(DATA_FILE)) {
            const raw = JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'));
            return {
                userNames:      raw.userNames      || {},
                welcomedUsers:  raw.welcomedUsers  || {},
                vipNumbers:     raw.vipNumbers     || [],
                vipExpiry:      raw.vipExpiry      || {},
                blacklist:      raw.blacklist      || [],
                userLanguages:  raw.userLanguages  || {},
                userLimits:     raw.userLimits     || {},
                userLimitsUsage:raw.userLimitsUsage|| {},
                stats:          raw.stats          || { totalMessages:0, totalImages:0, totalDocs:0 },
            };
        }
    } catch(e) { console.error('[loadData]', e.message); }
    return { userNames:{}, welcomedUsers:{}, vipNumbers:[], vipExpiry:{}, blacklist:[], userLanguages:{}, userLimits:{}, userLimitsUsage:{}, stats:{totalMessages:0,totalImages:0,totalDocs:0} };
}

let _saveTimer = null;
let { userNames, welcomedUsers, vipNumbers, vipExpiry, blacklist, userLanguages, userLimits, userLimitsUsage, stats } = loadData();

function saveData() {
    if (_saveTimer) return;
    _saveTimer = setTimeout(() => {
        _saveTimer = null;
        try {
            fs.writeFileSync(DATA_FILE, JSON.stringify({ userNames, welcomedUsers, vipNumbers, vipExpiry, blacklist, userLanguages, userLimits, userLimitsUsage, stats }, null, 2), 'utf8');
        } catch(e) { console.error('[saveData]', e.message); }
    }, 800);
}

// RAM state
let userChats      = {};
let userPdfContext = {};
let userTTSPending = {};
let userChatLastSeen = {};
const _spamCheck   = {};
const _lastNotify  = {};
const _lastMsgTime = {};
const _qaCache     = new Map();

// ============================================================
// LIMITS HELPERS
// ============================================================
function getUserDailyLimit(id) {
    return userLimits[id] != null ? userLimits[id] : DAILY_MSG_LIMIT;
}
function getDailyRecord(id) {
    if (!userLimitsUsage[id]) userLimitsUsage[id] = { messages:0, images:0, docs:0, tts:0, activatedAt:Date.now() };
    return userLimitsUsage[id];
}
function resetUserUsage(id) {
    userLimitsUsage[id] = { messages:0, images:0, docs:0, tts:0, activatedAt:Date.now() };
    saveData();
}
function checkDailyMessages(id) {
    const limit = getUserDailyLimit(id);
    const rec = getDailyRecord(id);
    if (rec.messages >= limit) return { allowed:false, remaining:0, limit, commit:()=>{} };
    return { allowed:true, remaining:limit-rec.messages-1, limit, commit:()=>{ rec.messages++; saveData(); } };
}
function checkDailyTTS(id) {
    const d = getDailyRecord(id);
    if (d.tts >= DAILY_TTS_LIMIT) return { allowed:false, remaining:0 };
    return { allowed:true, remaining:DAILY_TTS_LIMIT-d.tts-1, commit:()=>{ d.tts++; saveData(); } };
}
function checkDailyLimit(id, type) {
    const d = getDailyRecord(id);
    if (type==='image') { if(d.images>=DAILY_IMG_LIMIT) return false; d.images++; saveData(); return true; }
    if (type==='pdf')   { if(d.docs>=10) return false; d.docs++; saveData(); return true; }
    return true;
}
function isActiveVIP(id) {
    const sid = String(id);
    if (!vipNumbers.includes(sid)) return false;
    const exp = vipExpiry[sid];
    if (!exp) return true;
    if (Date.now() > exp) {
        vipNumbers = vipNumbers.filter(n=>n!==sid);
        delete vipExpiry[sid];
        saveData();
        tgSend(id, '⚠️ انتهت صلاحية اشتراكك المميز (VIP).\nللتجديد تواصل مع المهندس نادر:\n👤 wa.me/972593850520').catch(()=>{});
        return false;
    }
    return true;
}
function checkVIPExpiry() {
    const now = Date.now();
    let changed = false;
    for (const num of [...vipNumbers]) {
        const exp = vipExpiry[num];
        if (exp && now > exp) {
            vipNumbers = vipNumbers.filter(n=>n!==num);
            delete vipExpiry[num];
            changed = true;
            tgSend(num, '⚠️ انتهت صلاحية اشتراكك المميز (VIP).\nللتجديد: wa.me/972593850520').catch(()=>{});
        }
    }
    if (changed) saveData();
}
function checkSpam(id) {
    const now = Date.now();
    const sid = String(id);
    if (!_spamCheck[sid]) _spamCheck[sid] = [];
    _spamCheck[sid] = _spamCheck[sid].filter(t => now - t < 5000);
    if (_spamCheck[sid].length >= 5) return false;
    _spamCheck[sid].push(now);
    return true;
}
function cleanMemory() {
    const keys = Object.keys(userChats);
    if (keys.length > 800) {
        const sorted = keys.sort((a,b)=>(userChatLastSeen[a]||0)-(userChatLastSeen[b]||0));
        sorted.slice(0, keys.length-800).forEach(k=>{ delete userChats[k]; delete userChatLastSeen[k]; });
    }
    const SIX = 6*60*60_000, now = Date.now();
    for (const k of Object.keys(userPdfContext))
        if (now - (userPdfContext[k]?.loadedAt||0) > SIX) delete userPdfContext[k];
    for (const [k,v] of _qaCache.entries())
        if (now - v.createdAt > 24*60*60_000) _qaCache.delete(k);
}
setInterval(cleanMemory, 60*60_000);
setInterval(checkVIPExpiry, 60*60_000);
setInterval(() => {
    const now = Date.now();
    for (const k of Object.keys(userTTSPending))
        if (now > (userTTSPending[k]?.expiresAt||0)) delete userTTSPending[k];
}, 10*60_000);

// ============================================================
// SYSTEM PROMPTS
// ============================================================
let _cachedSystemPrompt = null;
let _cachedPromptDate   = '';

function getSystemPrompt() {
    const now = new Date();
    const dateStr = now.toLocaleDateString('ar-SA', { timeZone:'Asia/Jerusalem', weekday:'long', year:'numeric', month:'long', day:'numeric' });
    const timeStr = now.toLocaleTimeString('ar-SA', { timeZone:'Asia/Jerusalem', hour:'2-digit', minute:'2-digit' });
    const today = now.toDateString();
    if (_cachedPromptDate !== today) {
        _cachedPromptDate = today;
        _cachedSystemPrompt =
            `اسمك "MedTerm"، مساعد ذكاء اصطناعي شامل على تيليغرام.\n` +
            `التاريخ: ${dateStr} - ${timeStr} (القدس). استخدمه دائماً عند السؤال عن التاريخ.\n\n` +
            `شخصيتك: مهني ودقيق، ردود مباشرة بدون حشو. اللغة الافتراضية عربية، تجيب بلغة المستخدم فوراً. تجيب على أي سؤال في أي مجال بدون استثناء.\n\n` +
            `قواعد الكتابة — مهمة جداً:\n` +
            `• لا تستخدم النجوم * أبداً في ردودك\n` +
            `• لا تستخدم الشرطة السفلية _ للتنسيق\n` +
            `• لا تستخدم # للعناوين\n` +
            `• لا تستخدم أي رموز Markdown\n` +
            `• اكتب بنص عادي واضح فقط\n` +
            `• للتعداد استخدم الأرقام (1. 2. 3.) أو النقطة •\n` +
            `• الكود البرمجي فقط يمكن كتابته بين علامتي backtick\n\n` +
            `مجالاتك: طب، علوم، برمجة، قانون، دين، تاريخ، أعمال، ترجمة، أدب، طبخ، وأي موضوع آخر.\n` +
            `اسم المستخدم في السياق، استخدمه أحياناً بشكل طبيعي.`;
    }
    return _cachedSystemPrompt;
}

function isMedicalQuery(text) {
    return /دواء|علاج|مرض|عرض|اعراض|أعراض|دم|سكر|ضغط|قلب|كلى|كبد|رئة|أشعة|عملية|جرعة|مضاد حيوي|مسكن|تشخيص|طبيب|مستشفى|صيدلية|فحص|نتيجة|تحليل|ألم|pain|fever|drug|medicine|dose|symptom|diagnosis|treatment/i.test(text||'');
}
function isComplexQuery(text) {
    return /تشخيص|خطة علاج|تحليل مفصل|اشرح بالتفصيل|قارن بين|ما الفرق بين|برمج|اكتب كود|code|برنامج|خوارزمية|قانون|عقد|فتوى|حكم شرعي|ترجم هذا النص|essay|مقال|تقرير|بحث|summarize|خلاصة شاملة/i.test(text||'');
}
function getSmartSystemPrompt(text, lang) {
    const base = getSystemPrompt();
    if (lang && lang !== 'ar') return base + `\n\nمهم: أجب بهذه اللغة دائماً: ${lang}`;
    return base;
}

// ============================================================
// QA CACHE
// ============================================================
const QA_CACHE_MAX = 500, QA_CACHE_TTL = 24*60*60_000;
function normalizeQ(text) {
    return (text||'').replace(/[\u064B-\u065F]/g,'').replace(/[،,.:؟?!]/g,'').replace(/\s+/g,' ').toLowerCase().trim().slice(0,120);
}
function qaGet(q) {
    const key = normalizeQ(q);
    const hit = _qaCache.get(key);
    if (!hit) return null;
    if (Date.now()-hit.createdAt > QA_CACHE_TTL) { _qaCache.delete(key); return null; }
    hit.hits++;
    return hit.answer;
}
function qaSet(q, answer) {
    const key = normalizeQ(q);
    if (key.length < 10) return;
    if (/رصيد|اشتراك|وقت|تاريخ|اليوم|الآن|الان|كم|عمري|اسمي/i.test(key)) return;
    if (_qaCache.size >= QA_CACHE_MAX) {
        const ks = [..._qaCache.keys()].slice(0,50);
        ks.forEach(k=>_qaCache.delete(k));
    }
    _qaCache.set(key, { answer, hits:0, createdAt:Date.now() });
}

// ============================================================
// TRIVIAL REPLIES
// ============================================================
const TRIVIAL = {
    ok:['حسناً 😊','تمام 👍'], okay:['حسناً 😊','تمام 👍'],
    تمام:['👍','تمام!','😊'], حسنا:['👍','حسناً!'], 'حسناً':['👍','حسناً!'],
    اوك:['👍','أوكيه!'], اوكيه:['👍','أوكيه!'],
    هه:['😄','هههه 😄'], هههه:['😄😄','هههه 😂'], lol:['😂','هههه 😂'],
    شكرا:['العفو 😊','بكل سرور 🌟'], 'شكراً':['العفو 😊'],
    thanks:["You're welcome! 😊",'Anytime! 🌟'], thank:["You're welcome! 😊"],
    باي:['إلى اللقاء 👋','مع السلامة 😊'], 'مع السلامة':['إلى اللقاء 👋'],
    goodbye:['Goodbye! 👋'], bye:['Goodbye! 👋'],
};
function getTrivialReply(text) {
    const t = (text||'').trim().toLowerCase().replace(/[!.،؟?]+$/,'').replace(/[\u064B-\u065F]/g,'');
    if (t.length < 3 && !/[a-zA-Z\u0600-\u06FF]/.test(t)) return '😊';
    const opts = TRIVIAL[t];
    if (opts) return opts[Math.floor(Math.random()*opts.length)];
    if (/^ه+$/.test(t)) return ['😄','😂','هههه 😄'][Math.floor(Math.random()*3)];
    if (/^[👍👌✅🙏😊❤️]+$/.test(text?.trim())) return '😊';
    return null;
}

// ============================================================
// SMART RATE DELAY
// ============================================================
async function smartRateDelay(id) {
    const now = Date.now(), last = _lastMsgTime[id]||0, diff = now-last;
    _lastMsgTime[id] = now;
    if (diff < 1000 && diff > 0) await new Promise(r=>setTimeout(r,2000));
}

// ============================================================
// CONTEXT
// ============================================================
function detectContextNeeded(body, history) {
    if (!history || history.length===0) return 2;
    const lastTopic = history.slice(-1)[0]?.content||'';
    const sameWords = (body||'').split(' ').filter(w=>w.length>3&&lastTopic.includes(w));
    if (sameWords.length>=2) return 8;
    if (isComplexQuery(body)) return 10;
    return 4;
}
function selectModel(text, histLen) {
    const isSimple = text.length<80 && histLen<=2 && !isMedicalQuery(text) && !isComplexQuery(text);
    if (isSimple) return { model:'mistral-small-latest', maxTok:600 };
    if (isComplexQuery(text)||text.length>700) return { model:'mistral-large-latest', maxTok:1200 };
    return { model:'mistral-small-latest', maxTok:900 };
}
async function compressContext(history) {
    if (!history||history.length<8) return history;
    try {
        const toCompress = history.slice(0,-4);
        const toKeep     = history.slice(-4);
        const convText   = toCompress.map(m=>`${m.role==='user'?'المستخدم':'المساعد'}: ${m.content.slice(0,200)}`).join('\n');
        const summary = await callMistral({ model:'mistral-small-latest', messages:[{role:'system',content:'لخّص هذه المحادثة في جملتين أو ثلاث.'},{role:'user',content:convText}], max_tokens:150, temperature:0.3 });
        return [{role:'user',content:`[ملخص المحادثة السابقة: ${summary}]`},{role:'assistant',content:'حسناً، أكمل معك.'}, ...toKeep];
    } catch { return history.slice(-6); }
}

// ============================================================
// FETCH HELPER
// ============================================================
async function fetchWithTimeout(url, options={}, timeoutMs=API_TIMEOUT_MS) {
    const controller = new AbortController();
    const timer = setTimeout(()=>controller.abort(), timeoutMs);
    try {
        return await fetch(url, { ...options, signal:controller.signal });
    } finally { clearTimeout(timer); }
}

// ============================================================
// AI SEMAPHORE
// ============================================================
const MAX_CONCURRENT_AI = 15;
let _aiActive = 0;
const _aiQueue = [];
function aiSemaphore() {
    return new Promise(resolve => {
        const tryAcquire = () => {
            if (_aiActive < MAX_CONCURRENT_AI) { _aiActive++; resolve(()=>{ _aiActive--; if(_aiQueue.length) _aiQueue.shift()(); }); }
            else _aiQueue.push(tryAcquire);
        };
        tryAcquire();
    });
}

// ============================================================
// MISTRAL API
// ============================================================
async function callMistral(payload, retries=3) {
    const release = await aiSemaphore();
    let lastError = new Error('لم تكتمل أي محاولة');
    try {
        for (let attempt=0; attempt<=retries; attempt++) {
            try {
                const response = await fetchWithTimeout('https://api.mistral.ai/v1/chat/completions', {
                    method:'POST',
                    headers:{ 'Content-Type':'application/json', 'Authorization':`Bearer ${MISTRAL_API_KEY}` },
                    body: JSON.stringify({ ...payload, stream:false })
                }, API_TIMEOUT_MS);
                if (response.status===401) throw new Error('AUTH_ERROR');
                if (response.status===429||response.status===529) {
                    const wait = Math.min(2000*Math.pow(2,attempt), 20000);
                    await new Promise(r=>setTimeout(r,wait));
                    continue;
                }
                if (!response.ok) throw new Error(`HTTP_${response.status}`);
                const data = await response.json();
                const content = data.choices?.[0]?.message?.content?.trim();
                if (!content) throw new Error('EMPTY_RESPONSE');
                return content;
            } catch(e) {
                lastError = e;
                if (e.message==='AUTH_ERROR'||e.name==='AbortError') throw e;
                if (attempt<retries) await new Promise(r=>setTimeout(r,1500*Math.pow(2,attempt)));
            }
        }
        throw lastError;
    } finally { release(); }
}

async function askAI(messages) {
    const lastUserMsg = [...messages].reverse().find(m=>m.role==='user')?.content||'';
    const histLen = messages.filter(m=>m.role!=='system').length;
    const { model, maxTok } = selectModel(lastUserMsg, histLen);
    try {
        return await callMistral({ model, messages, max_tokens:maxTok, temperature:0.5 });
    } catch(e) {
        const fallbacks = [{model:'mistral-small-latest',maxTok:900},{model:'mistral-large-latest',maxTok:1200}].filter(f=>f.model!==model);
        for (const fb of fallbacks) {
            try { return await callMistral({ model:fb.model, messages, max_tokens:fb.maxTok, temperature:0.5 }); } catch {}
        }
        if (e.name==='AbortError') return 'الرد يأخذ وقتاً أطول من المعتاد، يرجى إعادة المحاولة.';
        if (e.message==='AUTH_ERROR') return 'عذراً، مشكلة في إعدادات الخدمة.';
        return 'عذراً، تعذّر الرد الآن. يرجى المحاولة مرة أخرى.';
    }
}

async function askAIWithImage(base64Image, userQuestion, userName, mimeType) {
    try {
        const mime = mimeType||'image/jpeg';
        const hasQ = userQuestion&&userQuestion.trim().length>0;
        const q = (userQuestion||'').toLowerCase();
        const wantsOCR = !hasQ || /اقرأ|استخرج|انسخ|نص|مكتوب|read|extract|ocr|text/i.test(q);
        const wantsMed = /أشعة|xray|mri|رنين|ct|تحليل دم|فحص|تقرير طبي|lab|blood|ecg/i.test(q)||isMedicalQuery(q);
        const wantsTbl = /جدول|table|بيانات|أرقام|excel/i.test(q);
        let systemPrompt, userPrompt, maxTok;
        if (wantsOCR && !hasQ) {
            systemPrompt = `أنت نظام OCR متخصص وعالي الدقة. اقرأ كل نص في الصورة بدقة 100% كما هو مكتوب. لا تغيّر أي شيء. اقرأ العربي من اليمين لليسار. بعد النص أضف تحليلاً مختصراً.`;
            userPrompt = 'اقرأ كل النصوص في هذه الصورة بدقة كاملة ثم حللها.';
            maxTok = 2000;
        } else if (wantsMed) {
            systemPrompt = `أنت طبيب متخصص في تحليل الصور الطبية. اقرأ الأرقام والقيم بدقة 100%. قارن بالمعدلات الطبيعية. وضّح: طبيعي ✅ أم غير طبيعي ⚠️. اختم بـ: راجع طبيبك للتشخيص النهائي.`;
            userPrompt = hasQ ? userQuestion : 'حلّل هذه الصورة الطبية بالتفصيل مع قراءة كل القيم.';
            maxTok = 2000;
        } else if (wantsTbl) {
            systemPrompt = 'أنت خبير في قراءة الجداول. اقرأ كل خلية بدقة مع الحفاظ على الهيكل.';
            userPrompt = hasQ ? userQuestion : 'اقرأ الجدول/البيانات بدقة كاملة.';
            maxTok = 2000;
        } else if (hasQ) {
            systemPrompt = 'أنت مساعد ذكي يجيب على الأسئلة المتعلقة بالصور. اقرأ النصوص بدقة واجب مباشرة من محتوى الصورة.';
            userPrompt = userQuestion;
            maxTok = 1500;
        } else {
            systemPrompt = 'أنت مساعد ذكي يصف الصور. صف كل ما تراه بدقة. اقرأ أي نص أو أرقام. الرد بالعربية.';
            userPrompt = 'صف هذه الصورة بالتفصيل الكامل.';
            maxTok = 1500;
        }
        return await callMistral({
            model:'pixtral-large-latest',
            messages:[
                {role:'system',content:systemPrompt},
                {role:'user',content:[
                    {type:'image_url',image_url:{url:`data:${mime};base64,${base64Image}`,detail:'high'}},
                    {type:'text',text:(userName?`(${userName})\n`:'')+userPrompt}
                ]}
            ],
            max_tokens:maxTok, temperature:0.1
        });
    } catch(e) {
        console.error('[askAIWithImage]',e.message);
        return 'عذراً، لم أتمكن من تحليل الصورة.';
    }
}

async function transcribeAndReplyAudio(buffer, mimeType, userQuestion, userName, chatHistory) {
    const b64 = buffer.toString('base64');
    const mime = mimeType||'audio/ogg';
    const hasQ = userQuestion&&userQuestion.trim().length>0;
    const systemPrompt = getSystemPrompt();
    const historyContext = (chatHistory||[]).slice(-6);
    try {
        return await callMistral({
            model:'voxtral-mini-latest',
            messages:[
                {role:'system',content:systemPrompt+(userName?`\n(المستخدم: ${userName})`:'')},
                ...historyContext,
                {role:'user',content:[
                    {type:'audio_url',audio_url:{url:`data:${mime};base64,${b64}`}},
                    ...(hasQ?[{type:'text',text:userQuestion}]:[])
                ]}
            ],
            max_tokens:1200, temperature:0.5
        });
    } catch(e) {
        if (e.message==='AUTH_ERROR') throw e;
        // Fallback: Whisper-style — نص ثم رد
        const transcribed = await callMistral({
            model:'mistral-large-latest',
            messages:[{role:'system',content:'استمع لهذه الرسالة الصوتية واكتب نصها الحرفي كاملاً بدون أي تعليق.'},{role:'user',content:[{type:'audio_url',audio_url:{url:`data:${mime};base64,${b64}`}}]}],
            max_tokens:800, temperature:0.1
        });
        return await askAI([{role:'system',content:systemPrompt},...historyContext,{role:'user',content:transcribed||(hasQ?userQuestion:'')}]);
    }
}

// ============================================================
// SMART TRANSLATE
// ============================================================
async function smartTranslate(text, targetLangCode) {
    try {
        const url = `https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=${targetLangCode}&dt=t&q=${encodeURIComponent(text)}`;
        const res = await fetchWithTimeout(url,{headers:{'User-Agent':'Mozilla/5.0'}},8_000);
        if (res.ok) {
            const data = await res.json();
            const translated = data?.[0]?.filter(Boolean)?.map(i=>i?.[0])?.filter(Boolean)?.join('')||'';
            if (translated.trim()) return { text:translated.trim(), source:'google' };
        }
    } catch(e) { console.warn('[translate] Google فشل:', e.message); }
    try {
        const res = await fetchWithTimeout(`https://api.mymemory.translated.net/get?q=${encodeURIComponent(text)}&langpair=auto|${targetLangCode}`,{},8_000);
        if (res.ok) {
            const data = await res.json();
            const t = data?.responseData?.translatedText||'';
            if (t&&!t.startsWith('MYMEMORY')&&t.trim()) return { text:t.trim(), source:'mymemory' };
        }
    } catch(e) { console.warn('[translate] MyMemory فشل:', e.message); }
    const targetLangName = targetLangCode==='ar'?'العربية':'English';
    const translated = await callMistral({
        model:'mistral-small-latest',
        messages:[{role:'system',content:`ترجم إلى ${targetLangName}. أرسل الترجمة فقط.`},{role:'user',content:text}],
        max_tokens:500, temperature:0.3
    });
    return { text:translated.trim(), source:'mistral' };
}

// ============================================================
// TTS
// ============================================================
function splitTextForTTS(text, maxLen=190) {
    const clean = (text||'').replace(/[*_#\[\](){}|\\^~`<>]/g,'').replace(/\s+/g,' ').trim();
    if (!clean) return [];
    if (clean.length<=maxLen) return [clean];
    const chunks=[]; let remaining=clean;
    while (remaining.length>0) {
        if (remaining.length<=maxLen) { chunks.push(remaining.trim()); break; }
        let cut=-1;
        for (const sep of ['. ','؟ ','! ','، ','؛ ','\n']) {
            const idx=remaining.lastIndexOf(sep,maxLen);
            if (idx>maxLen*0.4) { cut=idx+sep.length-1; break; }
        }
        if (cut<=0) cut=remaining.lastIndexOf(' ',maxLen);
        if (cut<=0) cut=maxLen;
        chunks.push(remaining.slice(0,cut).trim());
        remaining=remaining.slice(cut).trim();
    }
    return chunks.filter(c=>c.length>0);
}

async function generateTTS(text, lang='en') {
    const ttsLang = lang==='ar'?'ar':'en';
    const chunks = splitTextForTTS(text);
    if (!chunks.length) throw new Error('نص فارغ');
    const tmpId = `${Date.now()}_${crypto.randomBytes(6).toString('hex')}`;
    const mp3Files = [];
    try {
        for (let i=0; i<chunks.length; i++) {
            const url = `https://translate.google.com/translate_tts?ie=UTF-8&q=${encodeURIComponent(chunks[i])}&tl=${ttsLang}&client=tw-ob&ttsspeed=0.9`;
            const response = await fetch(url);
            if (!response.ok) throw new Error(`TTS HTTP ${response.status}`);
            const buf = Buffer.from(await response.arrayBuffer());
            if (!buf||buf.length<100) throw new Error('MP3 فارغ');
            const mp3File = path.join(os.tmpdir(), `tts_tg_${tmpId}_${i}.mp3`);
            await fs.promises.writeFile(mp3File, buf);
            mp3Files.push(mp3File);
            if (i<chunks.length-1) await new Promise(r=>setTimeout(r,150));
        }
        const oggFile = path.join(os.tmpdir(), `tts_tg_${tmpId}_out.ogg`);
        if (mp3Files.length===1) {
            await new Promise((res,rej)=>execFile('ffmpeg',['-y','-i',mp3Files[0],'-c:a','libopus','-b:a','32k','-vn',oggFile],{timeout:30_000},(err)=>err?rej(err):res()));
        } else {
            const inputArgs=[]; mp3Files.forEach(f=>{inputArgs.push('-i',f);});
            const filterInputs=mp3Files.map((_,i)=>`[${i}:a]`).join('');
            await new Promise((res,rej)=>execFile('ffmpeg',['-y',...inputArgs,'-filter_complex',`${filterInputs}concat=n=${mp3Files.length}:v=0:a=1[out]`,'-map','[out]','-c:a','libopus','-b:a','32k',oggFile],{timeout:120_000},(err)=>err?rej(err):res()));
        }
        const oggBuffer = await fs.promises.readFile(oggFile);
        fs.unlink(oggFile,()=>{});
        return oggBuffer;
    } finally {
        for (const f of mp3Files) fs.unlink(f,()=>{});
    }
}

// ============================================================
// AUDIO DURATION
// ============================================================
async function getAudioDurationSeconds(buffer) {
    const tmpFile = path.join(os.tmpdir(),`dur_tg_${Date.now()}.ogg`);
    try {
        await fs.promises.writeFile(tmpFile, buffer);
        const duration = await new Promise((res,rej)=>{
            execFile('ffprobe',['-v','quiet','-print_format','json','-show_streams',tmpFile],{timeout:10_000},(err,stdout)=>{
                if(err) return rej(err);
                try { const dur=parseFloat(JSON.parse(stdout)?.streams?.[0]?.duration||'0'); res(isNaN(dur)?null:Math.ceil(dur)); } catch { res(null); }
            });
        });
        return duration;
    } catch { return null; }
    finally { fs.unlink(tmpFile,()=>{}); }
}

// ============================================================
// PDF CACHE
// ============================================================
if (!fs.existsSync(PDF_CACHE_DIR)) fs.mkdirSync(PDF_CACHE_DIR, { recursive:true });

function pdfCacheKey(fileName, buffer) {
    const hash = crypto.createHash('md5').update(buffer).digest('hex').slice(0,12);
    return `${fileName.replace(/[^a-zA-Z0-9]/g,'_').slice(0,30)}_${hash}`;
}
async function pdfCacheGet(key) {
    try {
        const file = path.join(PDF_CACHE_DIR, `${key}.json`);
        if (!fs.existsSync(file)) return null;
        const age = Date.now() - fs.statSync(file).mtimeMs;
        if (age > 30*24*60*60_000) { fs.unlinkSync(file); return null; }
        return JSON.parse(fs.readFileSync(file,'utf8'));
    } catch { return null; }
}
async function pdfCacheSet(key, fileName, docText, pageCount) {
    try {
        const file = path.join(PDF_CACHE_DIR, `${key}.json`);
        fs.writeFileSync(file, JSON.stringify({ fileName, docText, pageCount, cachedAt:Date.now() }), 'utf8');
    } catch {}
}

// ============================================================
// NOTIFY ADMIN
// ============================================================
async function notifyAdmin(message) {
    if (!ADMIN_TG_ID) return;
    const key = message.slice(0,30);
    const now = Date.now();
    if (_lastNotify[key] && now-_lastNotify[key] < 30*60_000) return;
    _lastNotify[key] = now;
    try { await tgSend(ADMIN_TG_ID, `🔔 *إشعار أدمن:*\n${message}`, {parse_mode:'Markdown'}); } catch {}
}

// ============================================================
// WELCOME MESSAGE
// ============================================================
function buildWelcome(name) {
    const first = name ? name.split(' ')[0] : null;
    const greeting = first ? `أهلاً ${first}` : 'أهلاً';
    return `${greeting} 👋\n\n*مرحباً بك في بوت MedTerm AI على تيليغرام!*\n\n` +
        `يمكنني مساعدتك في:\n` +
        `🏥 شرح ومساعدتك في أي سؤال\n` +
        `💊 معلومات شاملة عن التخصصات الطبية وباقي التخصصات\n` +
        `⚕️ الإجابة على الأسئلة بشكل عام\n` +
        `🤖 المساعدة في أي موضوع عام\n` +
        `🖼️ تحليل الصور والتقارير\n` +
        `📄 قراءة وتحليل ملفات PDF\n` +
        `🔊 نطق المصطلحات والكلمات صوتياً\n` +
        `🌐 الترجمة مع الصوت والنطق\n\n` +
        `─────────────────\n` +
        `✍️ *فقط أرسل سؤالك وسأرد عليك مباشرة!*`;
}

// ============================================================
// QUOTA EXCEEDED MESSAGE
// ============================================================
function buildQuotaMsg() {
    return `*«عزيزي المستخدم»*\n\n` +
        `*لقد انتهت الفترة التجريبية*\n\n` +
        `يمكنك الآن الاشتراك في بوت MedTerm AI مساعدك الذكي المربوط في الذكاء الاصطناعي\n\n` +
        `*ميزات البوت*\n\n` +
        `*1-* بحث دقيق (إجابات دقيقة وموثوقة)\n` +
        `*2-* مربوط في (ديب سيك+جيميني+شات جي بي تي)\n` +
        `*3-* اشتراك مدفوع وبدون حدود\n` +
        `*4-* يمكن إرسال الرسائل قدر ما تشاء\n` +
        `*5-* يمكنك إرسال صور قدر ما تشاء\n` +
        `*6-* يمكنك البحث عن أي معلومة في الذكاء الاصطناعي\n` +
        `*7-* يعمل حتى لو الإنترنت ضعيف\n\n` +
        `*ملاحظة*\n` +
        `5 شيكل فقط في الشهر — أرخص بـ 20 مرة من المنافسين\n\n` +
        `*طرق الدفع* (جوال باي أو بال باي)\n\n` +
        `الرقم: 0597111855\n` +
        `باسم: *إياد معروف*\n\n` +
        `بعد التحويل راسل المهندس نادر:\n` +
        `https://wa.me/972593850520`;
}

// ============================================================
// TELEGRAM API WRAPPER
// ============================================================
const TG_API = `https://api.telegram.org/bot${TELEGRAM_TOKEN}`;

async function tgRequest(method, body={}) {
    const res = await fetchWithTimeout(`${TG_API}/${method}`, {
        method:'POST',
        headers:{'Content-Type':'application/json'},
        body:JSON.stringify(body)
    }, 30_000);
    const data = await res.json();
    if (!data.ok) throw new Error(`[TG:${method}] ${data.description||'unknown error'}`);
    return data.result;
}

// إرسال رسالة عادية — بدون Markdown (للمستخدمين)
async function tgSend(chatId, text, extra={}) {
    // نحذف أي نجوم متبقية من رد الـ AI احتياطاً
    const cleanText = (text||'').replace(/\*([^*]+)\*/g, '$1').replace(/\_([^_]+)\_/g, '$1');
    const chunks = splitTgMessage(cleanText);
    for (let i=0; i<chunks.length; i++) {
        await tgRequest('sendMessage', { chat_id:chatId, text:chunks[i], ...extra });
        if (i<chunks.length-1) await new Promise(r=>setTimeout(r,300));
    }
}

// إرسال رسالة بـ Markdown — للوحة التحكم والأدمن فقط
async function tgSendMD(chatId, text, extra={}) {
    const chunks = splitTgMessage(text);
    for (let i=0; i<chunks.length; i++) {
        await tgRequest('sendMessage', { chat_id:chatId, text:chunks[i], parse_mode:'Markdown', ...extra });
        if (i<chunks.length-1) await new Promise(r=>setTimeout(r,300));
    }
}

async function tgEdit(chatId, msgId, text, extra={}) {
    try {
        await tgRequest('editMessageText', { chat_id:chatId, message_id:msgId, text, parse_mode:'Markdown', ...extra });
    } catch(e) {
        if (!e.message.includes('not modified')) console.error('[tgEdit]', e.message);
    }
}

async function tgAnswerCallback(callbackId, text='', alert=false) {
    await tgRequest('answerCallbackQuery', { callback_query_id:callbackId, text, show_alert:alert }).catch(()=>{});
}

async function tgSendTyping(chatId) {
    await tgRequest('sendChatAction', { chat_id:chatId, action:'typing' }).catch(()=>{});
}
async function tgSendAudioAction(chatId) {
    await tgRequest('sendChatAction', { chat_id:chatId, action:'record_voice' }).catch(()=>{});
}
async function tgSendDocumentAction(chatId) {
    await tgRequest('sendChatAction', { chat_id:chatId, action:'upload_document' }).catch(()=>{});
}

async function tgSendVoice(chatId, oggBuffer, replyToId=null) {
    const form = new FormData();
    form.append('chat_id', String(chatId));
    form.append('voice', new Blob([oggBuffer],{type:'audio/ogg'}), 'voice.ogg');
    if (replyToId) form.append('reply_to_message_id', String(replyToId));
    const res = await fetchWithTimeout(`${TG_API}/sendVoice`, { method:'POST', body:form }, 60_000);
    const data = await res.json();
    if (!data.ok) throw new Error(`[tgSendVoice] ${data.description}`);
    return data.result;
}

function splitTgMessage(text, maxLen=4000) {
    if (!text||text.length<=maxLen) return [text||''];
    const chunks=[]; let remaining=text;
    while (remaining.length>0) {
        if (remaining.length<=maxLen) { chunks.push(remaining); break; }
        let cut = remaining.lastIndexOf('\n', maxLen);
        if (cut<=0) cut = remaining.lastIndexOf(' ', maxLen);
        if (cut<=0) cut = maxLen;
        chunks.push(remaining.slice(0,cut));
        remaining = remaining.slice(cut).trimStart();
    }
    return chunks.filter(c=>c.length>0);
}

async function tgDownloadFile(fileId) {
    const fileInfo = await tgRequest('getFile', { file_id:fileId });
    const fileUrl  = `https://api.telegram.org/file/bot${TELEGRAM_TOKEN}/${fileInfo.file_path}`;
    const res = await fetchWithTimeout(fileUrl, {}, 60_000);
    if (!res.ok) throw new Error(`[tgDownloadFile] HTTP ${res.status}`);
    const arrayBuffer = await res.arrayBuffer();
    return { buffer:Buffer.from(arrayBuffer), filePath:fileInfo.file_path };
}

// ============================================================
// ADMIN DASHBOARD — لوحة التحكم الكاملة بأزرار Inline
// ============================================================

// حالة الأدمن في لوحة التحكم (انتظار إدخال)
const _adminState = {}; // { chatId: { action, data } }

// ── بناء لوحة التحكم الرئيسية ──
function buildMainDashboard() {
    const totalUsers = Object.keys(welcomedUsers).length;
    const activeNow  = Object.keys(userChats).filter(id=>userChats[id]?.length>0).length;
    const vipCount   = vipNumbers.length;
    const blCount    = blacklist.length;
    const now = new Date().toLocaleString('ar-SA', { timeZone:'Asia/Jerusalem' });

    const text =
        `🎛️ *لوحة تحكم MedTerm AI — تيليغرام*\n` +
        `━━━━━━━━━━━━━━━━━━━━\n\n` +
        `🕐 ${now}\n\n` +
        `📊 *نظرة عامة:*\n` +
        `👥 إجمالي المستخدمين: *${totalUsers}*\n` +
        `🟢 نشطون الآن: *${activeNow}*\n` +
        `⭐ مستخدمو VIP: *${vipCount}*\n` +
        `⛔ محظورون: *${blCount}*\n\n` +
        `📈 *الإحصائيات الكلية:*\n` +
        `💬 الرسائل: *${stats.totalMessages||0}*\n` +
        `🖼️ الصور: *${stats.totalImages||0}*\n` +
        `📄 الملفات: *${stats.totalDocs||0}*\n` +
        `🧠 جلسات في الذاكرة: *${Object.keys(userChats).length}*`;

    const keyboard = {
        inline_keyboard: [
            [
                { text:'👥 المستخدمون', callback_data:'dash:users:0' },
                { text:'⭐ VIP', callback_data:'dash:vip' }
            ],
            [
                { text:'⛔ المحظورون', callback_data:'dash:blacklist' },
                { text:'📊 إحصائيات', callback_data:'dash:stats' }
            ],
            [
                { text:'➕ تفعيل VIP', callback_data:'dash:addvip_prompt' },
                { text:'➖ إزالة VIP', callback_data:'dash:removevip_prompt' }
            ],
            [
                { text:'🚫 حظر مستخدم', callback_data:'dash:block_prompt' },
                { text:'✅ رفع حظر', callback_data:'dash:unblock_prompt' }
            ],
            [
                { text:'📢 بث جماعي', callback_data:'dash:broadcast_prompt' },
                { text:'🔄 تصفير رصيد', callback_data:'dash:reset_prompt' }
            ],
            [
                { text:'🔔 الإشعارات', callback_data:'dash:notifications' },
                { text:'🔁 تحديث', callback_data:'dash:refresh' }
            ]
        ]
    };
    return { text, keyboard };
}

// ── قائمة المستخدمين مع التفاصيل ──
function buildUsersList(page=0, perPage=5) {
    const allIds = Object.keys(welcomedUsers);
    const total  = allIds.length;
    const start  = page * perPage;
    const pageIds = allIds.slice(start, start + perPage);

    let text = `👥 *المستخدمون* (${start+1}-${Math.min(start+perPage, total)} من ${total})\n━━━━━━━━━━━━━━━━━━━━\n\n`;

    for (const id of pageIds) {
        const name    = userNames[id] || '(بدون اسم)';
        const isVIP   = vipNumbers.includes(id);
        const isBL    = blacklist.includes(id);
        const rec     = userLimitsUsage[id] || {};
        const lastSeen = userChatLastSeen[id] ? new Date(userChatLastSeen[id]).toLocaleString('ar-SA',{timeZone:'Asia/Jerusalem'}) : 'لم يتفاعل';
        const badge   = isVIP ? '⭐' : isBL ? '⛔' : '👤';

        text +=
            `${badge} *${name}*\n` +
            `🆔 ID: \`${id}\`\n` +
            `💬 رسائل: ${rec.messages||0} | 🖼️ صور: ${rec.images||0} | 📄 ملفات: ${rec.docs||0}\n` +
            `🕐 آخر نشاط: ${lastSeen}\n\n`;
    }

    const buttons = [];
    // أزرار إدارة سريعة لكل مستخدم
    for (const id of pageIds) {
        const name = (userNames[id]||id).slice(0,15);
        const isVIP = vipNumbers.includes(id);
        const isBL  = blacklist.includes(id);
        buttons.push([
            { text: `${isVIP?'⭐':'➕VIP'} ${name}`, callback_data: isVIP ? `dash:removevip:${id}` : `dash:addvip:${id}` },
            { text: `${isBL?'✅رفع':'🚫حظر'} ${name}`, callback_data: isBL ? `dash:unblock:${id}` : `dash:block:${id}` },
            { text: `🔄 تصفير ${name}`, callback_data: `dash:reset:${id}` }
        ]);
    }

    // أزرار التنقل
    const navRow = [];
    if (page > 0) navRow.push({ text:'◀️ السابق', callback_data:`dash:users:${page-1}` });
    navRow.push({ text:`${page+1}/${Math.ceil(total/perPage)||1}`, callback_data:'dash:noop' });
    if (start+perPage < total) navRow.push({ text:'التالي ▶️', callback_data:`dash:users:${page+1}` });
    buttons.push(navRow);
    buttons.push([{ text:'🔙 الرئيسية', callback_data:'dash:main' }]);

    return { text, keyboard: { inline_keyboard: buttons } };
}

// ── قائمة VIP ──
function buildVIPList() {
    if (!vipNumbers.length) {
        return {
            text: '⭐ *قائمة VIP فارغة*\n\nلا يوجد مستخدمون VIP حتى الآن.',
            keyboard: { inline_keyboard: [[{text:'➕ تفعيل VIP جديد', callback_data:'dash:addvip_prompt'},{text:'🔙 رجوع', callback_data:'dash:main'}]] }
        };
    }
    let text = `⭐ *مستخدمو VIP* (${vipNumbers.length})\n━━━━━━━━━━━━━━━━━━━━\n\n`;
    const buttons = [];
    for (const id of vipNumbers) {
        const name = userNames[id]||'(بدون اسم)';
        const exp  = vipExpiry[id];
        const expStr = exp ? new Date(exp).toLocaleDateString('ar-SA',{timeZone:'Asia/Jerusalem'}) : 'دائم';
        text += `⭐ *${name}*\n🆔 \`${id}\`\n📅 ينتهي: ${expStr}\n\n`;
        buttons.push([
            { text:`➖ إزالة VIP — ${name.slice(0,15)}`, callback_data:`dash:removevip:${id}` }
        ]);
    }
    buttons.push([{text:'🔙 الرئيسية', callback_data:'dash:main'}]);
    return { text, keyboard:{ inline_keyboard:buttons } };
}

// ── قائمة المحظورين ──
function buildBlacklist() {
    if (!blacklist.length) {
        return {
            text: '⛔ *قائمة الحظر فارغة*\n\nلا يوجد مستخدمون محظورون.',
            keyboard: { inline_keyboard: [[{text:'🚫 حظر مستخدم', callback_data:'dash:block_prompt'},{text:'🔙 رجوع', callback_data:'dash:main'}]] }
        };
    }
    let text = `⛔ *المحظورون* (${blacklist.length})\n━━━━━━━━━━━━━━━━━━━━\n\n`;
    const buttons = [];
    for (const id of blacklist) {
        const name = userNames[id]||'(بدون اسم)';
        text += `⛔ *${name}*\n🆔 \`${id}\`\n\n`;
        buttons.push([{ text:`✅ رفع حظر — ${name.slice(0,15)}`, callback_data:`dash:unblock:${id}` }]);
    }
    buttons.push([{text:'🔙 الرئيسية', callback_data:'dash:main'}]);
    return { text, keyboard:{ inline_keyboard:buttons } };
}

// ── الإحصائيات التفصيلية ──
function buildDetailedStats() {
    const allIds = Object.keys(welcomedUsers);
    const vipIds = vipNumbers;
    const now = Date.now();

    // أكثر المستخدمين نشاطاً
    const sorted = allIds
        .map(id=>({ id, msgs:(userLimitsUsage[id]?.messages||0) }))
        .sort((a,b)=>b.msgs-a.msgs)
        .slice(0,5);

    let text =
        `📊 *الإحصائيات التفصيلية*\n━━━━━━━━━━━━━━━━━━━━\n\n` +
        `👥 *المستخدمون:*\n` +
        `• إجمالي: ${allIds.length}\n` +
        `• VIP: ${vipIds.length}\n` +
        `• محظورون: ${blacklist.length}\n` +
        `• نشطون (جلسة): ${Object.keys(userChats).filter(id=>userChats[id]?.length>0).length}\n\n` +
        `📈 *الاستخدام الكلي:*\n` +
        `• 💬 رسائل: ${stats.totalMessages||0}\n` +
        `• 🖼️ صور محللة: ${stats.totalImages||0}\n` +
        `• 📄 ملفات PDF: ${stats.totalDocs||0}\n\n` +
        `🏆 *الأكثر استخداماً:*\n`;

    for (let i=0; i<sorted.length; i++) {
        const u = sorted[i];
        const name = userNames[u.id]||u.id;
        text += `${i+1}. ${name} — ${u.msgs} رسالة\n`;
    }

    return {
        text,
        keyboard:{ inline_keyboard:[
            [{text:'🔙 الرئيسية', callback_data:'dash:main'},{text:'🔁 تحديث', callback_data:'dash:stats'}]
        ]}
    };
}

// ── إشعارات ──
function buildNotificationsPanel() {
    const text =
        `🔔 *إعدادات الإشعارات*\n━━━━━━━━━━━━━━━━━━━━\n\n` +
        `الإشعارات الفورية مفعّلة تلقائياً:\n\n` +
        `✅ مستخدم جديد يدخل\n` +
        `✅ انتهاء رصيد مستخدم\n` +
        `✅ انتهاء VIP تلقائياً\n` +
        `✅ أخطاء API\n\n` +
        `_كل هذه الإشعارات تصلك فور حدوثها._`;
    return {
        text,
        keyboard:{ inline_keyboard:[
            [{text:'📢 بث جماعي الآن', callback_data:'dash:broadcast_prompt'}],
            [{text:'🔙 الرئيسية', callback_data:'dash:main'}]
        ]}
    };
}

// ── إرسال/تحديث لوحة التحكم ──
async function sendDashboard(chatId, msgIdToEdit=null) {
    const { text, keyboard } = buildMainDashboard();
    if (msgIdToEdit) {
        await tgEdit(chatId, msgIdToEdit, text, { reply_markup: keyboard });
    } else {
        await tgRequest('sendMessage', { chat_id:chatId, text, parse_mode:'Markdown', reply_markup:keyboard });
    }
}

// ============================================================
// CALLBACK QUERY HANDLER — معالج أزرار لوحة التحكم
// ============================================================
async function handleCallback(update) {
    const cb      = update.callback_query;
    if (!cb) return;

    const chatId   = cb.message?.chat?.id;
    const msgId    = cb.message?.message_id;
    const userId   = cb.from?.id;
    const data     = cb.data||'';

    if (!chatId||!msgId) { await tgAnswerCallback(cb.id); return; }
    if (!ADMIN_TG_ID || String(userId) !== String(ADMIN_TG_ID)) {
        await tgAnswerCallback(cb.id, '⛔ غير مصرح لك', true);
        return;
    }

    await tgAnswerCallback(cb.id);

    try {
        // ── الرئيسية ──
        if (data==='dash:main'||data==='dash:refresh') {
            await sendDashboard(chatId, msgId);
            return;
        }
        if (data==='dash:noop') return;

        // ── المستخدمون ──
        if (data.startsWith('dash:users:')) {
            const page = parseInt(data.split(':')[2]||'0',10);
            const { text, keyboard } = buildUsersList(page);
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── VIP قائمة ──
        if (data==='dash:vip') {
            const { text, keyboard } = buildVIPList();
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── تفعيل VIP مباشرة من قائمة المستخدمين ──
        if (data.startsWith('dash:addvip:')) {
            const id = data.split(':')[2];
            if (!vipNumbers.includes(id)) {
                vipNumbers.push(id);
                vipExpiry[id] = Date.now()+30*24*60*60_000;
                resetUserUsage(id);
                saveData();
                await tgSend(id, 'تهانينا! تم تفعيل اشتراكك المميز (VIP)\nرسائل وصور وصوت غير محدودة ✨').catch(()=>{});
                await tgRequest('answerCallbackQuery',{callback_query_id:cb.id,text:`✅ تم تفعيل VIP للـ ID: ${id}`,show_alert:true}).catch(()=>{});
            }
            const page = 0;
            const { text, keyboard } = buildUsersList(page);
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── إزالة VIP مباشرة ──
        if (data.startsWith('dash:removevip:')) {
            const id = data.split(':')[2];
            const was = vipNumbers.includes(id);
            vipNumbers = vipNumbers.filter(n=>n!==id);
            delete vipExpiry[id];
            saveData();
            if (was) await tgSend(id, 'ℹ️ تم إلغاء اشتراكك المميز (VIP).').catch(()=>{});
            await tgRequest('answerCallbackQuery',{callback_query_id:cb.id,text:was?`✅ تم إزالة VIP`:'لم يكن VIP',show_alert:true}).catch(()=>{});
            const { text, keyboard } = buildVIPList();
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── حظر مباشر ──
        if (data.startsWith('dash:block:')) {
            const id = data.split(':')[2];
            // ✅ حماية: لا يمكن حظر الأدمن
            if (String(id) === String(ADMIN_TG_ID)) {
                await tgRequest('answerCallbackQuery',{callback_query_id:cb.id,text:'⛔ لا يمكن حظر الأدمن',show_alert:true}).catch(()=>{});
                return;
            }
            if (!blacklist.includes(id)) { blacklist.push(id); saveData(); }
            await tgRequest('answerCallbackQuery',{callback_query_id:cb.id,text:`⛔ تم حظر ${id}`,show_alert:true}).catch(()=>{});
            const page = 0;
            const { text, keyboard } = buildUsersList(page);
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── رفع حظر مباشر ──
        if (data.startsWith('dash:unblock:')) {
            const id = data.split(':')[2];
            const idx = blacklist.indexOf(id);
            if (idx>-1) { blacklist.splice(idx,1); saveData(); }
            await tgRequest('answerCallbackQuery',{callback_query_id:cb.id,text:`✅ تم رفع الحظر`,show_alert:true}).catch(()=>{});
            const { text, keyboard } = buildBlacklist();
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── تصفير رصيد مباشر ──
        if (data.startsWith('dash:reset:')) {
            const id = data.split(':')[2];
            resetUserUsage(id);
            await tgRequest('answerCallbackQuery',{callback_query_id:cb.id,text:`✅ تم تصفير رصيد ${id}`,show_alert:true}).catch(()=>{});
            return;
        }

        // ── Blacklist قائمة ──
        if (data==='dash:blacklist') {
            const { text, keyboard } = buildBlacklist();
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── إحصائيات ──
        if (data==='dash:stats') {
            const { text, keyboard } = buildDetailedStats();
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── الإشعارات ──
        if (data==='dash:notifications') {
            const { text, keyboard } = buildNotificationsPanel();
            await tgEdit(chatId, msgId, text, { reply_markup:keyboard });
            return;
        }

        // ── Prompts (طلب إدخال) ──
        if (data==='dash:addvip_prompt') {
            _adminState[chatId] = { action:'addvip', msgId };
            await tgEdit(chatId, msgId,
                '➕ *تفعيل VIP*\n\nأرسل *Telegram ID* للمستخدم الذي تريد تفعيل VIP له:\n_(مثال: 123456789)_',
                { reply_markup:{ inline_keyboard:[[{text:'❌ إلغاء', callback_data:'dash:main'}]] } }
            );
            return;
        }
        if (data==='dash:removevip_prompt') {
            _adminState[chatId] = { action:'removevip', msgId };
            await tgEdit(chatId, msgId,
                '➖ *إزالة VIP*\n\nأرسل *Telegram ID* للمستخدم:',
                { reply_markup:{ inline_keyboard:[[{text:'❌ إلغاء', callback_data:'dash:main'}]] } }
            );
            return;
        }
        if (data==='dash:block_prompt') {
            _adminState[chatId] = { action:'block', msgId };
            await tgEdit(chatId, msgId,
                '🚫 *حظر مستخدم*\n\nأرسل *Telegram ID* للمستخدم:',
                { reply_markup:{ inline_keyboard:[[{text:'❌ إلغاء', callback_data:'dash:main'}]] } }
            );
            return;
        }
        if (data==='dash:unblock_prompt') {
            _adminState[chatId] = { action:'unblock', msgId };
            await tgEdit(chatId, msgId,
                '✅ *رفع الحظر*\n\nأرسل *Telegram ID* للمستخدم:',
                { reply_markup:{ inline_keyboard:[[{text:'❌ إلغاء', callback_data:'dash:main'}]] } }
            );
            return;
        }
        if (data==='dash:broadcast_prompt') {
            _adminState[chatId] = { action:'broadcast', msgId };
            await tgEdit(chatId, msgId,
                '📢 *بث جماعي*\n\nأرسل نص الرسالة التي تريد إرسالها لجميع المستخدمين:',
                { reply_markup:{ inline_keyboard:[[{text:'❌ إلغاء', callback_data:'dash:main'}]] } }
            );
            return;
        }
        if (data==='dash:reset_prompt') {
            _adminState[chatId] = { action:'reset', msgId };
            await tgEdit(chatId, msgId,
                '🔄 *تصفير رصيد*\n\nأرسل *Telegram ID* للمستخدم:',
                { reply_markup:{ inline_keyboard:[[{text:'❌ إلغاء', callback_data:'dash:main'}]] } }
            );
            return;
        }
    } catch(e) {
        console.error('[handleCallback]', e.message);
    }
}

// ============================================================
// ADMIN STATE — معالجة إدخالات الأدمن بعد الضغط على الأزرار
// ============================================================
async function handleAdminInput(chatId, senderId, text, msgId) {
    const state = _adminState[chatId];
    if (!state) return false;
    if (String(senderId) !== String(ADMIN_TG_ID)) return false;

    const { action, msgId:dashMsgId } = state;
    delete _adminState[chatId];

    // حذف رسالة الأدمن النصية
    await tgRequest('deleteMessage', { chat_id:chatId, message_id:msgId }).catch(()=>{});

    switch(action) {
        case 'addvip': {
            const id = text.trim().replace(/\D/g,'');
            if (!id) { await sendDashboard(chatId, dashMsgId); return true; }
            if (!vipNumbers.includes(id)) {
                vipNumbers.push(id);
                vipExpiry[id] = Date.now()+30*24*60*60_000;
                resetUserUsage(id);
                saveData();
                await tgSend(id, 'تهانينا! تم تفعيل اشتراكك المميز (VIP)\nرسائل وصور وصوت غير محدودة ✨').catch(()=>{});
                await tgSend(chatId, `✅ تم تفعيل VIP للـ ID: \`${id}\` (${userNames[id]||'مستخدم'})`);
            } else {
                await tgSend(chatId, `⚠️ \`${id}\` VIP أصلاً.`);
            }
            await sendDashboard(chatId, dashMsgId);
            return true;
        }
        case 'removevip': {
            const id = text.trim().replace(/\D/g,'');
            if (!id) { await sendDashboard(chatId, dashMsgId); return true; }
            const was = vipNumbers.includes(id);
            vipNumbers = vipNumbers.filter(n=>n!==id);
            delete vipExpiry[id];
            saveData();
            if (was) {
                await tgSend(id, 'ℹ️ تم إلغاء اشتراكك المميز (VIP).').catch(()=>{});
                await tgSend(chatId, `✅ تم إزالة VIP عن \`${id}\`.`);
            } else {
                await tgSend(chatId, `⚠️ \`${id}\` لم يكن VIP.`);
            }
            await sendDashboard(chatId, dashMsgId);
            return true;
        }
        case 'block': {
            const id = text.trim().replace(/\D/g,'');
            if (!id) { await sendDashboard(chatId, dashMsgId); return true; }
            if (String(id) === String(ADMIN_TG_ID)) {
                await tgSend(chatId, '⛔ لا يمكن حظر حساب الأدمن.');
                await sendDashboard(chatId, dashMsgId);
                return true;
            }
            if (!blacklist.includes(id)) { blacklist.push(id); saveData(); }
            await tgSend(chatId, `⛔ تم حظر \`${id}\`.`);
            await sendDashboard(chatId, dashMsgId);
            return true;
        }
        case 'unblock': {
            const id = text.trim().replace(/\D/g,'');
            if (!id) { await sendDashboard(chatId, dashMsgId); return true; }
            const idx = blacklist.indexOf(id);
            if (idx>-1) { blacklist.splice(idx,1); saveData(); }
            await tgSend(chatId, `✅ تم رفع الحظر عن \`${id}\`.`);
            await sendDashboard(chatId, dashMsgId);
            return true;
        }
        case 'reset': {
            const id = text.trim().replace(/\D/g,'');
            if (!id) { await sendDashboard(chatId, dashMsgId); return true; }
            resetUserUsage(id);
            await tgSend(chatId, `✅ تم تصفير رصيد \`${id}\`.`);
            await sendDashboard(chatId, dashMsgId);
            return true;
        }
        case 'broadcast': {
            const msg = text.trim();
            if (!msg) { await sendDashboard(chatId, dashMsgId); return true; }
            const allUsers = Object.keys(welcomedUsers).filter(id=>id!==String(ADMIN_TG_ID));
            let sent=0, failed=0;
            await tgSendMD(chatId, `📢 جاري الإرسال لـ ${allUsers.length} مستخدم...`);
            for (const uid of allUsers) {
                try { await tgSend(uid, msg); sent++; await new Promise(r=>setTimeout(r,300)); }
                catch { failed++; }
            }
            await tgSend(chatId, `📢 *انتهى البث:*\n✅ وصل: ${sent}\n❌ فشل: ${failed}`);
            await sendDashboard(chatId, dashMsgId);
            return true;
        }
    }
    return false;
}

// ============================================================
// MESSAGE HANDLER
// ============================================================
async function handleMessage(update) {
    const msg    = update.message || update.edited_message;
    if (!msg) return;

    const chatId   = msg.chat.id;
    const senderId = String(msg.from?.id||chatId);
    // ✅ المقارنة بـ String لتجنب خطأ Number vs String
    const isAdmin  = ADMIN_TG_ID > 0 && String(msg.from?.id) === String(ADMIN_TG_ID);
    const isGroup  = msg.chat.type === 'group' || msg.chat.type === 'supergroup';
    const msgId    = msg.message_id;

    // دوال الرد المحلية
    const reply = async (text) => tgSend(chatId, text, { reply_to_message_id:msgId });
    const react = async (emoji) => { /* تيليغرام يدعم الـ reactions في API متأخر */ };

    // ============================================================
    // فحص الحظر — الأدمن لا يُحظر أبداً حتى لو أُضيف للقائمة بالخطأ
    // ============================================================
    if (!isAdmin && blacklist.includes(senderId)) {
        const now = Date.now();
        const lastBl = _lastNotify[`bl_${senderId}`]||0;
        if (now-lastBl > 60*60_000) {
            _lastNotify[`bl_${senderId}`] = now;
            await reply('⛔ عذراً، تم حظرك من استخدام هذا البوت.\nللاستفسار: wa.me/972593850520');
        }
        return;
    }

    // ============================================================
    // استخراج النص
    // ============================================================
    const body = (msg.text||msg.caption||'').trim();
    const msgType = msg.text ? 'text' :
                    msg.photo ? 'photo' :
                    msg.voice||msg.audio ? 'audio' :
                    msg.document ? 'document' :
                    msg.video ? 'video' : 'unknown';

    // اسم المستخدم
    let userName = userNames[senderId];
    const tgName = [msg.from?.first_name, msg.from?.last_name].filter(Boolean).join(' ').trim() || msg.from?.username || '';
    if (tgName && tgName !== userName) {
        userNames[senderId] = tgName;
        userName = tgName;
        saveData();
    }

    console.log(`📨 [TG ${isAdmin?'ADMIN':'USER'}] ${senderId} (${userName||'?'}) | ${msgType} | "${body.slice(0,50)}"`);

    // ============================================================
    // رسالة الترحيب
    // ============================================================
    // ============================================================
    // رسالة الترحيب + إشعار الأدمن بمستخدم جديد
    // ============================================================
    if (!welcomedUsers[senderId]) {
        welcomedUsers[senderId] = true;
        userChats[senderId] = [];
        if (userName) {
            userChats[senderId].push({role:'user',content:`[اسم المستخدم: ${userName}]`});
            userChats[senderId].push({role:'assistant',content:`أهلاً ${userName}، كيف أستطيع مساعدتك؟`});
        }
        saveData();
        await reply(buildWelcome(userName));

        // ✅ إشعار الأدمن بمستخدم جديد مع كل التفاصيل
        const username_tg = msg.from?.username ? `@${msg.from.username}` : '(بدون username)';
        await notifyAdmin(
            `👤 *مستخدم جديد دخل البوت!*\n\n` +
            `الاسم: *${userName||'(بدون اسم)'}*\n` +
            `🆔 ID: \`${senderId}\`\n` +
            `📱 Username: ${username_tg}\n` +
            `🌐 اللغة: ${msg.from?.language_code||'غير معروفة'}\n` +
            `📅 الوقت: ${new Date().toLocaleString('ar-SA',{timeZone:'Asia/Jerusalem'})}\n\n` +
            `إجمالي المستخدمين الآن: *${Object.keys(welcomedUsers).length}*`
        );

        if (!body && msgType==='text') return;
    }

    userChatLastSeen[senderId] = Date.now();

    // ============================================================
    // لوحة التحكم — /admin أو !لوحة
    // ============================================================
    if (isAdmin && (body==='/admin'||body==='!لوحة'||body==='!dashboard')) {
        await sendDashboard(chatId);
        return;
    }

    // ============================================================
    // معالجة إدخالات الأدمن (بعد الضغط على أزرار اللوحة)
    // ============================================================
    if (isAdmin && _adminState[chatId]) {
        const handled = await handleAdminInput(chatId, userId, body, msgId);
        if (handled) return;
    }

    // ============================================================
    // أوامر الأدمن النصية (للتوافق مع الإصدار القديم)
    // ============================================================
    if (isAdmin) {
        const removeVipM = body.match(/^!removevip\s+(\d+)/i);
        if (removeVipM) {
            const num = removeVipM[1];
            const was = vipNumbers.includes(num);
            vipNumbers = vipNumbers.filter(n=>n!==num);
            delete vipExpiry[num];
            saveData();
            if (was) await tgSend(num, 'ℹ️ تم إلغاء اشتراكك المميز (VIP).').catch(()=>{});
            await reply(was ? `✅ تم إزالة VIP عن ${num}.` : `⚠️ ${num} لم يكن VIP.`);
            return;
        }
        const addVipM = body.match(/^!addvip\s+(\d+)/i);
        if (addVipM) {
            const num = addVipM[1];
            if (!vipNumbers.includes(num)) {
                vipNumbers.push(num);
                vipExpiry[num] = Date.now()+30*24*60*60_000;
                resetUserUsage(num);
                saveData();
                await tgSend(num, 'تهانينا! تم تفعيل اشتراكك المميز (VIP)\nرسائل وصور وصوت غير محدودة ✨').catch(()=>{});
                await reply(`✅ تم تفعيل VIP للـ ID: ${num} لمدة شهر.`);
            } else {
                await reply(`⚠️ ${num} VIP أصلاً.`);
            }
            return;
        }
        const resetM = body.match(/^!resetlimit\s+(\d+)/i);
        if (resetM) {
            resetUserUsage(resetM[1]);
            await reply(`✅ تم تصفير استهلاك ${resetM[1]}.`);
            return;
        }
        const blackM = body.match(/^!block\s+(\d+)/i);
        if (blackM) {
            const num = blackM[1];
            // ✅ حماية: لا يمكن حظر الأدمن أبداً
            if (String(num) === String(ADMIN_TG_ID)) {
                await reply('⛔ لا يمكن حظر حساب الأدمن.');
                return;
            }
            if (!blacklist.includes(num)) { blacklist.push(num); saveData(); }
            await reply(`⛔ تم حظر \`${num}\`.`);
            return;
        }
        const unblockM = body.match(/^!unblock\s+(\d+)/i);
        if (unblockM) {
            const num = unblockM[1];
            const idx = blacklist.indexOf(num);
            if (idx>-1) { blacklist.splice(idx,1); saveData(); }
            await reply(`✅ تم رفع الحظر عن ${num}.`);
            return;
        }
        if (body === '!stats') {
            const { text } = buildDetailedStats();
            await reply(text);
            return;
        }
        if (body.startsWith('!broadcast ')) {
            const text = body.slice(11).trim();
            if (!text) { await reply('❌ اكتب نص البث بعد الأمر.'); return; }
            const allUsers = Object.keys(welcomedUsers).filter(id=>id!==String(ADMIN_TG_ID));
            let sent=0, failed=0;
            for (const uid of allUsers) {
                try { await tgSend(uid, text); sent++; await new Promise(r=>setTimeout(r,500)); }
                catch { failed++; }
            }
            await reply(`📢 انتهى البث:\n✅ وصل: ${sent}\n❌ فشل: ${failed}`);
            return;
        }
    }

    // ============================================================
    // أوامر المستخدم
    // ============================================================
    if (body === '/start' || body === '!مساعدة' || body === '/help') {
        await reply(
            `📋 *قائمة الأوامر المتاحة:*\n\n` +
            `• /start أو !مساعدة — عرض هذه القائمة\n` +
            `• !مسح — مسح سياق المحادثة\n` +
            `• !رصيد — عرض الرصيد المتبقي\n` +
            `• !لغة en — تغيير لغة الردود\n` +
            `• !ملخص — تلخيص المحادثة\n\n` +
            `*🔊 الصوت:*\n` +
            `• نطق [نص] — تحويل النص لصوت\n` +
            `• أرسل رسالة صوتية — يفهمها ويرد\n` +
            `• أرسل صوت + كتابة !نص — يستخرج النص\n\n` +
            `*📄 الملفات:*\n` +
            `• أرسل PDF — وضع الملف تلقائي\n` +
            `• صفحة [رقم] — شرح صفحة\n` +
            `• ملخص — ملخص الملف\n` +
            `• خروج — خروج من وضع الملف\n\n` +
            `*🌐 الترجمة:*\n` +
            `• ترجم [نص] — ترجمة فورية مع صوت\n\n` +
            `_أرسل أي صورة لتحليلها أو قراءة نصوصها_`
        );
        return;
    }

    if (body === '!مسح' || body === '/reset') {
        userChats[senderId] = [];
        await reply('🗑️ تم مسح سياق المحادثة. يمكنك البدء من جديد! 👋');
        return;
    }

    if (body === '!رصيد' || body === '/balance') {
        const isVIP = isActiveVIP(senderId);
        if (isAdmin || isVIP) {
            await reply('♾️ *رصيدك غير محدود* (VIP/أدمن)\n\n💬 رسائل: ♾️\n🖼️ صور: ♾️\n🔊 صوت: ♾️\n📄 PDF: ♾️');
        } else {
            const limit = getUserDailyLimit(senderId);
            const rec = getDailyRecord(senderId);
            await reply(
                `📊 *رصيدك — النسخة المجانية:*\n\n` +
                `💬 الرسائل: ${rec.messages||0}/${limit} — متبقي: *${Math.max(0,limit-(rec.messages||0))}*\n` +
                `🖼️ الصور: ${rec.images||0}/${DAILY_IMG_LIMIT} — متبقي: *${Math.max(0,DAILY_IMG_LIMIT-(rec.images||0))}*\n` +
                `🔊 الصوت: ${rec.tts||0}/${DAILY_TTS_LIMIT} — متبقي: *${Math.max(0,DAILY_TTS_LIMIT-(rec.tts||0))}*\n\n` +
                `💎 للنسخة المميزة (VIP):\n👤 wa.me/972593850520`
            );
        }
        return;
    }

    if (body.match(/^!لغة\s+(\S+)/i)||body.match(/^!lang\s+(\S+)/i)) {
        const lang = (body.match(/^!(?:لغة|lang)\s+(\S+)/i)||[])[1]||'';
        if (lang) {
            userLanguages[senderId] = lang.toLowerCase();
            saveData();
            const names = {ar:'العربية',en:'الإنجليزية',fr:'الفرنسية',de:'الألمانية',es:'الإسبانية',tr:'التركية'};
            await reply(`🌐 تم تغيير اللغة إلى: *${names[lang.toLowerCase()]||lang}*`);
        } else {
            await reply(`🌐 لغتك الحالية: *${userLanguages[senderId]||'ar'}*\nمثال: !لغة en`);
        }
        return;
    }

    if (body === '!ملخص' || body === '/summary') {
        const history = userChats[senderId]||[];
        if (history.length<2) { await reply('📝 لا يوجد محادثة كافية للتلخيص بعد.'); return; }
        await tgSendTyping(chatId);
        const convText = history.slice(-20).map(m=>`${m.role==='user'?'المستخدم':'البوت'}: ${m.content.slice(0,300)}`).join('\n');
        try {
            const summary = await callMistral({ model:'mistral-small-latest', messages:[{role:'system',content:'لخّص هذه المحادثة في 5-7 نقاط.'},{role:'user',content:convText}], max_tokens:600, temperature:0.3 });
            await reply(`📝 *ملخص المحادثة:*\n\n${summary}`);
        } catch { await reply('عذراً، حدث خطأ أثناء التلخيص.'); }
        return;
    }

    // ============================================================
    // وضع PDF النشط
    // ============================================================
    if (userPdfContext[senderId]) {
        const { fileName, docText, pages, pageCount } = userPdfContext[senderId];

        if (/^خروج$/i.test(body)) {
            delete userPdfContext[senderId];
            userChats[senderId] = [];
            await reply('✅ تم الخروج من وضع الملف.');
            return;
        }

        if (!checkSpam(senderId)) { await reply('⚠️ أرسلت رسائل بشكل متسارع.'); return; }
        await tgSendTyping(chatId);

        // شرح صفحة
        const pageM = body.match(/^(?:صفحة|page)\s*(\d+)$/i);
        if (pageM) {
            const pageNum = parseInt(pageM[1], 10);
            const totalPages = pageCount || (pages?.length||0);
            if (pageNum<1||(totalPages>0&&pageNum>totalPages)) {
                await reply(`❌ رقم الصفحة غير صحيح. الملف يحتوي ${totalPages} صفحة.`);
                return;
            }
            let res;
            if (pages && pages[pageNum-1]) {
                res = await callMistral({ model:'pixtral-large-latest', messages:[{role:'system',content:`اشرح محتوى صفحة من الملف: "${fileName}" باللغة العربية.`},{role:'user',content:[{type:'image_url',image_url:{url:`data:image/jpeg;base64,${pages[pageNum-1]}`}},{type:'text',text:`اشرح محتوى الصفحة ${pageNum} بالتفصيل.`}]}], max_tokens:1200, temperature:0.3 });
            } else {
                const charsPerPage = Math.ceil(Math.min(docText.length,10000)/(totalPages||1));
                const start = (pageNum-1)*charsPerPage;
                res = await callMistral({ model:'mistral-large-latest', messages:[{role:'system',content:`اشرح محتوى صفحة من الملف: "${fileName}".`},{role:'user',content:`اشرح الصفحة ${pageNum}:\n${docText.slice(start,start+charsPerPage)}`}], max_tokens:1000, temperature:0.3 });
            }
            if (!userChats[senderId]) userChats[senderId]=[];
            userChats[senderId].push({role:'user',content:`[طلب شرح صفحة ${pageNum}]`});
            userChats[senderId].push({role:'assistant',content:res});
            await reply(`📄 *شرح الصفحة ${pageNum} من "${fileName}":*\n\n${res}`);
            return;
        }

        // ملخص
        if (/^ملخص$|^summary$/i.test(body)) {
            let res;
            if (docText && docText.length>200) {
                res = await callMistral({ model:'mistral-large-latest', messages:[{role:'system',content:`ملخص شامل للملف: "${fileName}" باللغة العربية.`},{role:'user',content:`محتوى الملف:\n${docText.slice(0,12000)}\n\nقدّم ملخصاً شاملاً.`}], max_tokens:1500, temperature:0.3 });
            } else if (pages&&pages.length>0) {
                const imgs = pages.slice(0,4).map(b64=>({type:'image_url',image_url:{url:`data:image/jpeg;base64,${b64}`}}));
                res = await callMistral({ model:'pixtral-large-latest', messages:[{role:'system',content:`ملخص الملف: "${fileName}".`},{role:'user',content:[...imgs,{type:'text',text:'قدّم ملخصاً شاملاً.'}]}], max_tokens:1500, temperature:0.3 });
            } else { res='لا يوجد محتوى كافٍ.'; }
            if (!userChats[senderId]) userChats[senderId]=[];
            userChats[senderId].push({role:'user',content:'[طلب ملخص]'});
            userChats[senderId].push({role:'assistant',content:res});
            await reply(`📋 *ملخص "${fileName}":*\n\n${res}`);
            return;
        }

        // سؤال عام
        const needsVisual = /رسم|مخطط|صورة|جدول|diagram|chart|figure|شكل/i.test(body);
        if (!userChats[senderId]) userChats[senderId]=[];
        const history = userChats[senderId].slice(-8);
        let res;
        if (needsVisual && pages && pages.length>0) {
            const pagesToSend = pages.slice(0,2);
            const imgs = pagesToSend.map(b64=>({type:'image_url',image_url:{url:`data:image/jpeg;base64,${b64}`}}));
            res = await callMistral({ model:'pixtral-large-latest', messages:[{role:'system',content:`مساعد ذكي يجيب من الملف: "${fileName}".`},...history,{role:'user',content:[...imgs,{type:'text',text:body}]}], max_tokens:1500, temperature:0.3 });
        } else {
            res = await callMistral({ model:'mistral-large-latest', messages:[{role:'system',content:`مساعد ذكي يجيب من الملف: "${fileName}".`},...history,{role:'user',content:`محتوى الملف:\n${docText.slice(0,12000)}\n\nسؤال: ${body}`}], max_tokens:1200, temperature:0.3 });
        }
        userChats[senderId].push({role:'user',content:body});
        userChats[senderId].push({role:'assistant',content:res});
        if (userChats[senderId].length>MAX_HISTORY) userChats[senderId]=userChats[senderId].slice(-MAX_HISTORY);
        await reply(res);
        return;
    }

    // ============================================================
    // TTS Pending — انتظار "نعم"
    // ============================================================
    if (userTTSPending[senderId] && Date.now()<userTTSPending[senderId].expiresAt) {
        if (/^(نعم|yes|اه|ايوه|أيوه|yep)$/i.test(body.trim())) {
            const { term, lang } = userTTSPending[senderId];
            delete userTTSPending[senderId];
            await tgSendAudioAction(chatId);
            try {
                const audio = await generateTTS(term, lang);
                await tgSendVoice(chatId, audio, msgId);
            } catch { await reply('عذراً، لم أتمكن من توليد الصوت.'); }
            return;
        }
        if (/^(لا|no|لأ)$/i.test(body.trim())) {
            delete userTTSPending[senderId];
            await reply('حسناً 👍');
            return;
        }
    }

    // ============================================================
    // معالجة الصور
    // ============================================================
    if (msgType === 'photo') {
        if (!checkSpam(senderId)) { await reply('⚠️ أرسلت رسائل بشكل متسارع.'); return; }
        const isVIP = isActiveVIP(senderId);
        if (!isAdmin && !isVIP && !checkDailyLimit(senderId,'image')) {
            await reply(`⚠️ وصلت للحد اليومي للصور (${DAILY_IMG_LIMIT} صور).\nللاشتراك المميز: wa.me/972593850520`);
            return;
        }
        await tgSendTyping(chatId);
        try {
            // أكبر صورة (آخر عنصر في المصفوفة)
            const photo = msg.photo[msg.photo.length-1];
            const { buffer } = await tgDownloadFile(photo.file_id);
            const base64 = buffer.toString('base64');
            const res = await askAIWithImage(base64, body||'', userName, 'image/jpeg');
            if (!userChats[senderId]) userChats[senderId]=[];
            userChats[senderId].push({role:'user',content:body?`[صورة + "${body}"]`:'[صورة]'});
            userChats[senderId].push({role:'assistant',content:res});
            stats.totalImages=(stats.totalImages||0)+1;
            saveData();
            const isVIPimg = isAdmin||isVIP;
            let finalRes = res;
            if (!isVIPimg) {
                const rec = getDailyRecord(senderId);
                finalRes += `\n\n─────────────\n_🖼️ صور: ${Math.max(0,DAILY_IMG_LIMIT-(rec.images||0))} متبقية_`;
            }
            await reply(finalRes);
        } catch(e) {
            console.error('[photo]', e.message);
            await reply('عذراً، لم أتمكن من تحليل الصورة.');
        }
        return;
    }

    // ============================================================
    // معالجة الصوت / Voice
    // ============================================================
    if (msgType === 'audio') {
        if (!checkSpam(senderId)) { await reply('⚠️ أرسلت رسائل بشكل متسارع.'); return; }
        const isVIPaudio = isAdmin||isActiveVIP(senderId);
        const maxSec = isVIPaudio ? AUDIO_MAX_SECONDS_VIP : AUDIO_MAX_SECONDS_FREE;
        let ttsQuota = null;
        if (!isAdmin && !isVIPaudio) {
            ttsQuota = checkDailyTTS(senderId);
            if (!ttsQuota.allowed) {
                await reply(`⚠️ وصلت للحد اليومي للرسائل الصوتية.\nللاشتراك المميز: wa.me/972593850520`);
                return;
            }
        }
        await tgSendTyping(chatId);
        try {
            const fileId = (msg.voice||msg.audio)?.file_id;
            const duration = (msg.voice||msg.audio)?.duration||0;
            if (duration > maxSec) {
                const maxMin = Math.floor(maxSec/60);
                const durMin = Math.floor(duration/60), durSec = duration%60;
                await reply(`⚠️ *الرسالة الصوتية طويلة جداً*\n\nمدتها: *${durMin}:${String(durSec).padStart(2,'0')}*\nالحد الأقصى: *${maxMin} دقيقة*\n\n${isVIPaudio?'':'\n💎 VIP: حتى 15 دقيقة\n👤 wa.me/972593850520'}`);
                return;
            }
            const { buffer, filePath } = await tgDownloadFile(fileId);
            const mime = filePath.endsWith('.mp3')?'audio/mpeg':'audio/ogg';

            // استخراج النص فقط إذا طلب
            const wantsText = /^(!نص|!text|استخرج النص|حول.{0,5}نص|نص فقط)$/i.test(body.trim());
            if (wantsText) {
                const transcribed = await transcribeAndReplyAudio(buffer, mime, 'استمع واكتب النص الحرفي فقط بدون أي رد.', userName, []);
                await reply(`📝 *النص المستخرج:*\n\n${transcribed}`);
                if (!isVIPaudio && ttsQuota) ttsQuota.commit?.();
                return;
            }

            if (!userChats[senderId]) userChats[senderId]=[];
            const res = await transcribeAndReplyAudio(buffer, mime, body, userName, userChats[senderId]);
            userChats[senderId].push({role:'user',content:body?`[صوت + "${body}"]`:'[رسالة صوتية]'});
            userChats[senderId].push({role:'assistant',content:res});
            stats.totalMessages=(stats.totalMessages||0)+1;
            saveData();

            let finalRes = `🎙️ ${res}`;
            if (!isVIPaudio) {
                const rec = getDailyRecord(senderId);
                finalRes += `\n\n─────────────\n_🔊 صوت: ${Math.max(0,DAILY_TTS_LIMIT-(rec.tts||0))} متبقية_`;
            }
            await reply(finalRes);

            // رد بصوت إذا طلب
            if (/رد بصوت|رد صوت|صوتي|voice reply/i.test(body)) {
                try {
                    const replyLang = /[\u0600-\u06FF]/.test(res)?'ar':'en';
                    const audio = await generateTTS(res, replyLang);
                    await tgSendVoice(chatId, audio);
                } catch {}
            }

            if (!isVIPaudio && ttsQuota) ttsQuota.commit?.();
        } catch(e) {
            console.error('[audio]', e.message);
            await reply('عذراً، لم أتمكن من معالجة الرسالة الصوتية.');
        }
        return;
    }

    // ============================================================
    // معالجة PDF
    // ============================================================
    if (msgType === 'document') {
        if (!checkSpam(senderId)) { await reply('⚠️ أرسلت رسائل بشكل متسارع.'); return; }
        if (!isAdmin && !isActiveVIP(senderId) && !checkDailyLimit(senderId,'pdf')) {
            await reply('⚠️ وصلت للحد اليومي للملفات (10 ملفات/يوم).');
            return;
        }
        const doc = msg.document;
        const mime = doc.mime_type||'';
        const fileName = doc.file_name||'ملف';
        if (mime !== 'application/pdf') {
            await reply(`📎 "${fileName}"\nالنوع غير مدعوم. أرسل ملف PDF فقط.`);
            return;
        }
        const isVIPpdf = isAdmin||isActiveVIP(senderId);
        const maxSize = isVIPpdf ? 20*1024*1024 : 5*1024*1024;
        if (doc.file_size && doc.file_size > maxSize) {
            await reply(`⚠️ حجم الملف كبير (${(doc.file_size/1024/1024).toFixed(1)}MB).\nالحد: ${isVIPpdf?'20MB':'5MB'}`);
            return;
        }
        await tgSendDocumentAction(chatId);
        await reply('⏳ جاري قراءة الملف واستخراج محتواه، انتظر لحظة...');
        try {
            const { buffer } = await tgDownloadFile(doc.file_id);
            if (!buffer||buffer.length<4||buffer.slice(0,4).toString('ascii')!=='%PDF') {
                await reply('❌ الملف ليس PDF حقيقياً.'); return;
            }
            if (buffer.length > maxSize) {
                await reply(`⚠️ حجم الملف (${(buffer.length/1024/1024).toFixed(1)}MB) تجاوز الحد المسموح.`); return;
            }

            // فحص الكاش
            const cacheKey = pdfCacheKey(fileName, buffer);
            const cacheHit = await pdfCacheGet(cacheKey);
            if (cacheHit) {
                const { docText, pageCount } = cacheHit;
                userPdfContext[senderId] = { fileName, docText, pages:null, pageCount, loadedAt:Date.now() };
                userChats[senderId] = [];
                stats.totalDocs=(stats.totalDocs||0)+1; saveData();
                await reply(`📄 *"${fileName}"*\n⚡ محفوظ مسبقاً (${pageCount} صفحة) — تم تحميله فوراً!\n\n✅ *وضع الملف مفعّل*\n• اسألني أي سؤال من الملف\n• اكتب *صفحة [رقم]* لشرح صفحة\n• اكتب *ملخص* للملخص\n• اكتب *خروج* للخروج`);
                return;
            }

            // استخراج جديد
            const tmpDir = path.join(os.tmpdir(), `pdf_tg_${Date.now()}_${crypto.randomBytes(6).toString('hex')}`);
            await fs.promises.mkdir(tmpDir, { recursive:true });
            try {
                const pdfPath = path.join(tmpDir,'input.pdf');
                await fs.promises.writeFile(pdfPath, buffer);
                await new Promise((res,rej)=>execFile('mutool',['convert','-o',path.join(tmpDir,'page-%d.jpg'),'-O','resolution=150',pdfPath],{timeout:60_000},(err,_,se)=>err?rej(new Error(se||err.message)):res()));
                const pageFiles = (await fs.promises.readdir(tmpDir)).filter(f=>f.startsWith('page-')&&f.endsWith('.jpg')).sort();
                if (!pageFiles.length) throw new Error('mutool لم ينتج صور');
                const pages = await Promise.all(pageFiles.map(f=>fs.promises.readFile(path.join(tmpDir,f)).then(b=>b.toString('base64'))));
                let docText='';
                try { const parsed=await pdfParse(buffer); docText=(parsed.text||'').trim(); } catch {}
                if (docText) await pdfCacheSet(cacheKey, fileName, docText, pageFiles.length);
                stats.totalDocs=(stats.totalDocs||0)+1; saveData();
                userPdfContext[senderId] = { fileName, docText, pages, pageCount:pageFiles.length, loadedAt:Date.now() };
                userChats[senderId] = [];
                await reply(`📄 *تم قراءة "${fileName}"* (${pageFiles.length} صفحة)\n\n✅ *وضع الملف مفعّل*\n• اسألني أي سؤال من الملف\n• اكتب *صفحة [رقم]* لشرح صفحة\n• اكتب *ملخص* للملخص\n• اكتب *خروج* للخروج`);
            } finally { await fs.promises.rm(tmpDir,{recursive:true,force:true}).catch(()=>{}); }
        } catch(e) {
            console.error('[pdf]', e.message);
            await reply(`❌ لم أتمكن من قراءة الملف: ${e.message.slice(0,100)}`);
        }
        return;
    }

    // ============================================================
    // رسائل نصية — TTS / ترجمة / ذكاء اصطناعي
    // ============================================================
    if (msgType !== 'text') return;
    if (!body) return;

    // TTS
    const ttsM = body.match(/^(?:نطق|صوت|اسمعني|اقرأ|نطقها?)\s+(.+)$/is) || (body.startsWith('صوت ')? {1:body.slice(4)}:null);
    if (ttsM) {
        const isVIP = isActiveVIP(senderId);
        let ttsQ = null;
        if (!isAdmin&&!isVIP) { ttsQ=checkDailyTTS(senderId); if(!ttsQ.allowed){await reply(`⚠️ وصلت للحد اليومي للصوت.\nللاشتراك: wa.me/972593850520`);return;} }
        const ttsText = ttsM[1].trim();
        if (ttsText.length>5000) { await reply('⚠️ النص طويل جداً (أكثر من 5000 حرف).'); return; }
        await tgSendAudioAction(chatId);
        if (ttsText.length>200) await reply('⏳ جاري تحويل النص لصوت...');
        try {
            const lang = /[\u0600-\u06FF]/.test(ttsText)?'ar':'en';
            const audio = await generateTTS(ttsText, lang);
            await tgSendVoice(chatId, audio, msgId);
            if (!isAdmin&&!isVIP&&ttsQ) ttsQ.commit?.();
        } catch(e) { console.error('[TTS]',e.message); await reply('❌ لم أتمكن من توليد الصوت.'); }
        return;
    }

    // ترجمة
    const transM = body.match(/^(?:ترجم|translate|ترجمة)\s+(.+)$/is);
    if (transM) {
        const isVIP = isActiveVIP(senderId);
        let ttsQ = null;
        if (!isAdmin&&!isVIP) { ttsQ=checkDailyTTS(senderId); if(!ttsQ.allowed){await reply('⚠️ وصلت للحد اليومي.');return;} }
        const textToTrans = transM[1].trim();
        await tgSendTyping(chatId);
        try {
            const isAr = /[\u0600-\u06FF]/.test(textToTrans);
            const targetCode = isAr?'en':'ar';
            const result = await smartTranslate(textToTrans, targetCode);
            const origLabel = isAr?'🇸🇦 الأصلي:':'🔤 Original:';
            const transLabel = isAr?'🇬🇧 الترجمة:':'🇸🇦 الترجمة:';
            await reply(`${origLabel} ${textToTrans}\n\n${transLabel} ${result.text}`);
            await new Promise(r=>setTimeout(r,300));
            const audio = await generateTTS(result.text, targetCode);
            await tgSendVoice(chatId, audio, msgId);
            if (!isAdmin&&!isVIP&&ttsQ) ttsQ.commit?.();
        } catch(e) { console.error('[trans]',e.message); await reply('❌ حدث خطأ أثناء الترجمة.'); }
        return;
    }

    // ============================================================
    // Spam / Rate
    // ============================================================
    if (!checkSpam(senderId)) { await reply('⚠️ أرسلت رسائل بشكل متسارع، انتظر ثوانٍ.'); return; }
    const trivial = getTrivialReply(body);
    if (trivial) { await reply(trivial); return; }
    await smartRateDelay(senderId);

    // Quota
    const isVIP = isActiveVIP(senderId);
    let _quotaCommit = null;
    if (!isAdmin&&!isVIP) {
        const quota = checkDailyMessages(senderId);
        if (!quota.allowed) {
            await reply(buildQuotaMsg());
            await notifyAdmin(`⚠️ المستخدم ${userName||senderId} انتهت فترته التجريبية.`);
            return;
        }
        _quotaCommit = quota.commit;
    }

    // QA Cache
    const cached = qaGet(body);
    if (cached) {
        if (_quotaCommit) _quotaCommit();
        await reply(cached + (isAdmin?'\n_(من الكاش ⚡)_':''));
        return;
    }

    await tgSendTyping(chatId);
    if (!userChats[senderId]) userChats[senderId]=[];

    if (userChats[senderId].length===0 && userName) {
        userChats[senderId].push({role:'user',content:`[اسم المستخدم: ${userName}]`});
        userChats[senderId].push({role:'assistant',content:`أهلاً ${userName}، كيف أستطيع مساعدتك؟`});
    }

    stats.totalMessages=(stats.totalMessages||0)+1;
    saveData();

    const maxHist = isVIP ? 60 : MAX_HISTORY;
    if (userChats[senderId].length>=maxHist) {
        userChats[senderId] = await compressContext(userChats[senderId]);
    }

    const contextNeeded = isVIP ? maxHist : detectContextNeeded(body, userChats[senderId]);
    userChats[senderId].push({role:'user',content:body});
    const trimmedHistory = userChats[senderId].slice(-contextNeeded);

    const smartPrompt = getSmartSystemPrompt(body, userLanguages[senderId]);
    const res = await askAI([{role:'system',content:smartPrompt}, ...trimmedHistory]);

    userChats[senderId].push({role:'assistant',content:res});
    if (userChats[senderId].length>maxHist) userChats[senderId]=userChats[senderId].slice(-maxHist);
    userChatLastSeen[senderId] = Date.now();

    qaSet(body, res);
    if (_quotaCommit) _quotaCommit();

    let finalRes = res;
    if (!isAdmin&&!isVIP) {
        const rec = getDailyRecord(senderId);
        const msgLeft = Math.max(0, getUserDailyLimit(senderId)-(rec.messages||0));
        finalRes += `\n\n─────────────\n_💬 رسائل: ${msgLeft} متبقية_`;
    }
    await reply(finalRes);

    // نطق المصطلحات الطبية التلقائي
    if (isMedicalQuery(body) && res.length>50) {
        const medTermMatch = res.match(/\b([A-Z][a-z]+(?:in|ol|ine|ate|ide|ase|itis|osis|emia|uria|pathy|logy)\b)/);
        if (medTermMatch) {
            const term = medTermMatch[1];
            userTTSPending[senderId] = { term, lang:'en', expiresAt:Date.now()+3*60_000 };
            await reply(`🔊 هل تريد سماع نطق *"${term}"*؟ أرسل *نعم* أو *لا*`);
        }
    }
}

// ============================================================
// POLLING — التشغيل بدون Webhook (أبسط على Termux)
// ============================================================
let _offset = 0;
let _isRunning = true;

async function poll() {
    while (_isRunning) {
        try {
            const updates = await tgRequest('getUpdates', {
                offset:_offset,
                timeout:30,
                allowed_updates:['message','edited_message','callback_query']
            });
            if (updates && updates.length) {
                for (const update of updates) {
                    _offset = update.update_id + 1;
                    if (update.callback_query) {
                        handleCallback(update).catch(e=>console.error('[handleCallback]', e.message));
                    } else {
                        handleMessage(update).catch(e=>console.error('[handleMessage]', e.message));
                    }
                }
            }
        } catch(e) {
            if (_isRunning) {
                console.error('[poll]', e.message);
                await new Promise(r=>setTimeout(r,3000));
            }
        }
    }
}

// ============================================================
// START
// ============================================================
(function checkDeps() {
    const { spawnSync } = require('child_process');
    function findTool(name) {
        try { const r=spawnSync('which',[name],{encoding:'utf8',timeout:3000}); if(!r.error&&r.status===0&&r.stdout.trim()) return r.stdout.trim(); } catch {}
        const paths=[`/data/data/com.termux/files/usr/bin/${name}`,`/usr/bin/${name}`,`/usr/local/bin/${name}`];
        for (const p of paths) { try { if(fs.existsSync(p)) return p; } catch {} }
        return null;
    }
    const mutool = findTool('mutool');
    if (!mutool) { console.error('❌ mutool غير مثبت: pkg install mupdf-tools'); process.exit(1); }
    const ffmpeg = findTool('ffmpeg');
    if (!ffmpeg) { console.error('❌ ffmpeg غير مثبت: pkg install ffmpeg'); process.exit(1); }
    console.log(`✅ mutool: ${mutool}`);
    console.log(`✅ ffmpeg: ${ffmpeg}`);
})();

// مسح الـ webhook القديم إن وُجد (نستخدم polling)
tgRequest('deleteWebhook').catch(()=>{});

// ✅ تأمين: تأكد من أن الأدمن ليس في قائمة الحظر أبداً
if (ADMIN_TG_ID > 0) {
    const adminStr = String(ADMIN_TG_ID);
    const idx = blacklist.indexOf(adminStr);
    if (idx > -1) {
        blacklist.splice(idx, 1);
        saveData();
        console.log('⚠️ تم إزالة الأدمن من قائمة الحظر تلقائياً');
    }
}

console.log(`🚀 جاري تشغيل ${BOT_NAME} (تيليغرام)...`);
cleanPdfCache();
poll().then(()=>console.log('Bot stopped.')).catch(e=>console.error('Fatal:', e));

process.on('SIGINT',  ()=>{ _isRunning=false; console.log('\n🛑 إيقاف البوت...'); process.exit(0); });
process.on('SIGTERM', ()=>{ _isRunning=false; process.exit(0); });

function cleanPdfCache() {
    try {
        if (!fs.existsSync(PDF_CACHE_DIR)) return;
        const files = fs.readdirSync(PDF_CACHE_DIR);
        const now = Date.now();
        for (const f of files) {
            const fp = path.join(PDF_CACHE_DIR,f);
            try { if (now-fs.statSync(fp).mtimeMs > 30*24*60*60_000) fs.unlinkSync(fp); } catch {}
        }
    } catch {}
}
