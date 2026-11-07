// Frame Window, by Snoww
// Ctrl + Right Alt opens the menu.
// Built for Geode 5.3.2. This single file holds the whole mod.

#include <Geode/Geode.hpp>
#include <Geode/modify/CCKeyboardDispatcher.hpp>
#include <Geode/ui/GeodeUI.hpp>
#include <Geode/utils/async.hpp>

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iterator>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace geode::prelude;

// BEGIN_GDR
// ===========================================================================
namespace gdr {

struct Input {
    int64_t frame = 0;      // game frame, 240 TPS
    int64_t btn = 0;        // 1 = jump/click, 2 = left, 3 = right
    bool down = false;      // press (true) or release (false)
    bool player2 = false;
    double subframe = 0.0;  // sub-frame offset as stored by xdBot
};

struct FrameFix {
    int64_t frame = 0;
    double x = 0.0;
    double y = 0.0;         // player 1 y-position: the y-axis reference
    double r = 0.0;         // player 1 rotation
};

struct Replay {
    std::string author;
    std::string description;
    std::string botName;
    std::string botVersion;
    std::string levelName;
    int64_t levelId = 0;
    int64_t coins = 0;
    int64_t seed = 0;
    int64_t lastRecordedFrame = 0;
    bool ldm = false;
    double duration = 0.0;
    double framerate = 0.0;
    double gameVersion = 0.0;
    double version = 0.0;
    std::vector<Input> inputs;
    std::vector<FrameFix> frameFixes;
};

namespace detail {

class Reader {
public:
    explicit Reader(std::vector<uint8_t> const& data) : m_data(data) {}

    bool done() const { return m_pos == m_data.size(); }

    uint8_t byte() {
        need(1);
        return m_data[m_pos++];
    }

    uint64_t be(size_t n) {
        need(n);
        uint64_t v = 0;
        for (size_t k = 0; k < n; ++k) v = (v << 8) | m_data[m_pos++];
        return v;
    }

    std::string bytes(size_t n) {
        need(n);
        std::string s(reinterpret_cast<char const*>(&m_data[m_pos]), n);
        m_pos += n;
        return s;
    }

    std::string string() {
        uint8_t b = byte();
        if (b >= 0xa0 && b <= 0xbf) return bytes(b & 0x1f);
        if (b == 0xd9) return bytes(be(1));
        if (b == 0xda) return bytes(be(2));
        if (b == 0xdb) return bytes(be(4));
        throw std::runtime_error("expected string");
    }

    size_t arrayHeader() {
        uint8_t b = byte();
        if (b >= 0x90 && b <= 0x9f) return b & 0x0f;
        if (b == 0xdc) return be(2);
        if (b == 0xdd) return be(4);
        throw std::runtime_error("expected array");
    }

    size_t mapHeader() {
        uint8_t b = byte();
        if (b >= 0x80 && b <= 0x8f) return b & 0x0f;
        if (b == 0xde) return be(2);
        if (b == 0xdf) return be(4);
        throw std::runtime_error("expected map");
    }

    bool boolean() {
        uint8_t b = byte();
        if (b == 0xc2) return false;
        if (b == 0xc3) return true;
        throw std::runtime_error("expected bool");
    }

    struct Number {
        double real;
        int64_t integer;
        bool isInt;
    };

    Number number() {
        uint8_t b = byte();
        if (b <= 0x7f) return { double(b), b, true };
        if (b >= 0xe0) { auto v = int8_t(b); return { double(v), v, true }; }
        switch (b) {
            case 0xca: { uint32_t u = uint32_t(be(4)); float f; std::memcpy(&f, &u, 4); return { double(f), 0, false }; }
            case 0xcb: { uint64_t u = be(8); double d; std::memcpy(&d, &u, 8); return { d, 0, false }; }
            case 0xcc: { auto v = be(1); return { double(v), int64_t(v), true }; }
            case 0xcd: { auto v = be(2); return { double(v), int64_t(v), true }; }
            case 0xce: { auto v = be(4); return { double(v), int64_t(v), true }; }
            case 0xcf: { auto v = be(8); return { double(v), int64_t(v), true }; }
            case 0xd0: { auto v = int8_t(be(1)); return { double(v), v, true }; }
            case 0xd1: { auto v = int16_t(be(2)); return { double(v), v, true }; }
            case 0xd2: { auto v = int32_t(be(4)); return { double(v), v, true }; }
            case 0xd3: { auto v = int64_t(be(8)); return { double(v), v, true }; }
            default: throw std::runtime_error("expected number");
        }
    }

    double real() { return number().real; }

    int64_t integer() {
        auto n = number();
        return n.isInt ? n.integer : int64_t(n.real);
    }

    // Skips any single MessagePack value.
    void skip() {
        uint8_t b = byte();
        if (b <= 0x7f || b >= 0xe0 || b == 0xc0 || b == 0xc2 || b == 0xc3) return;
        if (b >= 0xa0 && b <= 0xbf) { bytes(b & 0x1f); return; }
        if (b >= 0x90 && b <= 0x9f) { for (size_t k = 0, n = b & 0x0f; k < n; ++k) skip(); return; }
        if (b >= 0x80 && b <= 0x8f) { for (size_t k = 0, n = (b & 0x0f) * 2u; k < n; ++k) skip(); return; }
        switch (b) {
            case 0xc4: bytes(be(1)); return;
            case 0xc5: bytes(be(2)); return;
            case 0xc6: bytes(be(4)); return;
            case 0xca: be(4); return;
            case 0xcb: be(8); return;
            case 0xcc: case 0xd0: be(1); return;
            case 0xcd: case 0xd1: be(2); return;
            case 0xce: case 0xd2: be(4); return;
            case 0xcf: case 0xd3: be(8); return;
            case 0xd9: bytes(be(1)); return;
            case 0xda: bytes(be(2)); return;
            case 0xdb: bytes(be(4)); return;
            case 0xdc: for (size_t k = 0, n = be(2); k < n; ++k) skip(); return;
            case 0xdd: for (size_t k = 0, n = be(4); k < n; ++k) skip(); return;
            case 0xde: for (size_t k = 0, n = be(2) * 2; k < n; ++k) skip(); return;
            case 0xdf: for (size_t k = 0, n = be(4) * 2; k < n; ++k) skip(); return;
            default: throw std::runtime_error("unsupported MessagePack type");
        }
    }

private:
    void need(size_t n) const {
        if (m_pos + n > m_data.size()) throw std::runtime_error("unexpected end of file");
    }

    std::vector<uint8_t> const& m_data;
    size_t m_pos = 0;
};

inline Input parseInput(Reader& r) {
    Input in;
    for (size_t n = r.mapHeader(), k = 0; k < n; ++k) {
        std::string key = r.string();
        if (key == "frame") in.frame = r.integer();
        else if (key == "btn") in.btn = r.integer();
        else if (key == "down") in.down = r.boolean();
        else if (key == "2p") in.player2 = r.boolean();
        else if (key == "subframe") in.subframe = r.real();
        else r.skip();
    }
    return in;
}

inline FrameFix parseFrameFix(Reader& r) {
    FrameFix ff;
    for (size_t n = r.mapHeader(), k = 0; k < n; ++k) {
        std::string key = r.string();
        if (key == "frame") ff.frame = r.integer();
        else if (key == "p1") {
            for (size_t m = r.mapHeader(), j = 0; j < m; ++j) {
                std::string sub = r.string();
                if (sub == "x") ff.x = r.real();
                else if (sub == "y") ff.y = r.real();
                else if (sub == "r") ff.r = r.real();
                else r.skip();
            }
        }
        else r.skip();  // player 2 is ignored
    }
    return ff;
}

} // namespace detail

// Parses the bytes of a .gdr file. Throws std::runtime_error if malformed.
inline Replay parse(std::vector<uint8_t> const& data) {
    detail::Reader r(data);
    Replay out;

    for (size_t n = r.mapHeader(), k = 0; k < n; ++k) {
        std::string key = r.string();
        if (key == "author") out.author = r.string();
        else if (key == "description") out.description = r.string();
        else if (key == "coins") out.coins = r.integer();
        else if (key == "seed") out.seed = r.integer();
        else if (key == "lastRecordedFrame") out.lastRecordedFrame = r.integer();
        else if (key == "ldm") out.ldm = r.boolean();
        else if (key == "duration") out.duration = r.real();
        else if (key == "framerate") out.framerate = r.real();
        else if (key == "gameVersion") out.gameVersion = r.real();
        else if (key == "version") out.version = r.real();
        else if (key == "bot") {
            for (size_t m = r.mapHeader(), j = 0; j < m; ++j) {
                std::string sub = r.string();
                if (sub == "name") out.botName = r.string();
                else if (sub == "version") out.botVersion = r.string();
                else r.skip();
            }
        }
        else if (key == "level") {
            for (size_t m = r.mapHeader(), j = 0; j < m; ++j) {
                std::string sub = r.string();
                if (sub == "id") out.levelId = r.integer();
                else if (sub == "name") out.levelName = r.string();
                else r.skip();
            }
        }
        else if (key == "inputs") {
            size_t count = r.arrayHeader();
            out.inputs.reserve(count);
            for (size_t j = 0; j < count; ++j) out.inputs.push_back(detail::parseInput(r));
        }
        else if (key == "frameFixes") {
            size_t count = r.arrayHeader();
            out.frameFixes.reserve(count);
            for (size_t j = 0; j < count; ++j) out.frameFixes.push_back(detail::parseFrameFix(r));
        }
        else r.skip();
    }
    return out;
}

} // namespace gdr
// END_GDR

// ===========================================================================
// PART 2: Frame-window analysis. Plain C++, no Geode.
// BEGIN_ANALYSIS
// ===========================================================================
namespace fw {

constexpr int kWindowFrames = 10;          // frame windows test offsets 0 to 9
constexpr int64_t kHorizon = 240;          // frames after a press that must keep matching (1 s at 240 FPS)
constexpr double kBisectTolerance = 1e-4;  // precision of CBF edges, in frames

enum class WindowMode { Frames, Cbf };

struct Click {
    int64_t frame;    // physics frame (240 FPS) the input lands on
    bool down;        // press (true) or release (false)
    double subframe;  // sub-frame value stored in the .gdr (used by CBF mode only)
};

struct YSample {
    int64_t frame;
    double x;
    double y;
};

struct Macro {
    std::string name;
    std::vector<Click> clicks;       // sorted by frame
    std::vector<YSample> reference;  // the replay's player positions, sorted by frame
};

// A trial runs the level with press `pressIndex` moved `offset` frames later
// and returns true if the run still matches the replay.
using Trial = std::function<bool(size_t pressIndex, double offset)>;

struct PressWindow {
    size_t pressIndex = 0;
    int64_t frame = 0;          // recorded press frame
    double frames = 0.0;        // whole frames (Frames mode) or a fraction (Cbf mode)
    bool reachedLimit = false;  // every offset from 0 to 9 matched
    int trials = 0;             // trials spent on this press
};

// The y-axis rule: for each frame from the press up to kHorizon frames later,
// the trial's y must be within `tolerance` of the replay's y.
// simulatedY[s] is the trial's y at frame (press + s).
bool yTrackMatches(Macro const& macro, size_t pressIndex, double tolerance,
                   std::vector<double> const& simulatedY) {
    int64_t start = macro.clicks[pressIndex].frame;
    auto it = std::lower_bound(macro.reference.begin(), macro.reference.end(), start,
        [](YSample const& r, int64_t f) { return r.frame < f; });

    size_t compared = 0;
    for (; it != macro.reference.end() && it->frame < start + kHorizon; ++it) {
        int64_t s = it->frame - start;
        if (s >= static_cast<int64_t>(simulatedY.size())) break;
        if (!(std::fabs(simulatedY[s] - it->y) <= tolerance)) return false;
        ++compared;
    }
    return compared > 0;
}

// Tests one press. Offsets are tried in order (0, 1, 2, ...) and the search stops
// at the first offset that fails, so a 5-frame press costs 6 trials and no more.
PressWindow measureWindow(Macro const& macro, size_t pressIndex, Trial const& trial, WindowMode mode) {
    PressWindow out;
    out.pressIndex = pressIndex;
    out.frame = macro.clicks[pressIndex].frame;

    int firstFail = -1;
    int passed = 0;
    for (int k = 0; k < kWindowFrames; ++k) {
        ++out.trials;
        if (!trial(pressIndex, k)) {
            firstFail = k;
            break;
        }
        passed = k + 1;
    }

    if (firstFail < 0) {  // all of 0 to 9 matched
        out.frames = kWindowFrames;
        out.reachedLimit = true;
        return out;
    }
    if (mode == WindowMode::Frames || firstFail == 0) {
        out.frames = passed;
        return out;
    }

    // CBF: the edge sits between the last passing frame and the first failing one.
    double lo = firstFail - 1.0;  // passes
    double hi = firstFail;        // fails
    while (hi - lo > kBisectTolerance) {
        double mid = (lo + hi) / 2.0;
        ++out.trials;
        if (trial(pressIndex, mid)) lo = mid;
        else hi = mid;
    }
    out.frames = (lo + hi) / 2.0;
    return out;
}

// Measures every press in the macro. Releases are skipped.
std::vector<PressWindow> analyzeWindows(Macro const& macro, Trial const& trial, WindowMode mode) {
    std::vector<PressWindow> out;
    for (size_t i = 0; i < macro.clicks.size(); ++i) {
        if (macro.clicks[i].down) out.push_back(measureWindow(macro, i, trial, mode));
    }
    return out;
}

} // namespace fw
// END_ANALYSIS

// ===========================================================================
// PART 3: Geode side. Settings, in-game trials, overlay, and menu.
// NOT COMPILED OR RUN YET: the GD calls below are written from the Geode API
// and CBF's source, and need an in-game test.
// ===========================================================================
namespace fw {

constexpr char const* kCBFId = "syzzi.click_between_frames";
constexpr ccColor3B kRed   { 235, 40, 80 };
constexpr ccColor3B kBlue  { 120, 180, 255 };
constexpr ccColor3B kWhite { 255, 255, 255 };
constexpr int kMenuTag    = 0x4657;
constexpr int kOverlayTag = 0x4658;

// Reads an xdBot .gdr file (MessagePack).
Result<Macro> parseGDR(std::filesystem::path const& path) {
    std::ifstream file(path, std::ios::binary);
    if (!file) return Err(std::string("Could not open ") + path.string());

    std::vector<uint8_t> data((std::istreambuf_iterator<char>(file)), {});
    try {
        auto replay = gdr::parse(data);

        Macro macro;
        macro.name = replay.levelName;
        for (auto const& in : replay.inputs) {
            if (in.btn == 1 && !in.player2) {
                macro.clicks.push_back({ in.frame, in.down, in.subframe });
            }
        }
        for (auto const& ff : replay.frameFixes) {
            macro.reference.push_back({ ff.frame, ff.x, ff.y });
        }
        return Ok(std::move(macro));
    } catch (std::exception const& e) {
        return Err(std::string("Invalid .gdr file: ") + e.what());
    }
}

// True when Click Between Frames is loaded and active. Its "soft-toggle"
// setting is true when CBF is disabled (see CBF's main.cpp).
bool cbfActive() {
    Mod* cbf = Loader::get()->getLoadedMod(kCBFId);
    return cbf && !cbf->getSettingValue<bool>("soft-toggle");
}

// Everything a run needs, kept between trials.
struct Session {
    Macro macro;
    std::vector<Ref<CheckpointObject>> checkpoints;  // one per click, saved just before it
};

Session g_session;

// Advances the level by one physics frame (240 FPS).
// TODO: confirm the game's own clock is stopped while the analysis runs.
void stepOnce(PlayLayer* pl) {
    pl->update(1.0f / 240.0f);
}

// Plays the whole recording once and saves a checkpoint right before each press.
// Returns false if the player dies, because the recording then does not match this level.
bool prepareSession(PlayLayer* pl, Session& s) {
    auto const& clicks = s.macro.clicks;
    if (clicks.empty()) return false;

    s.checkpoints.assign(clicks.size(), Ref<CheckpointObject>());
    pl->resetLevel();

    size_t next = 0;
    int64_t last = clicks.back().frame;
    for (int64_t f = 0; f <= last; ++f) {
        for (size_t k = next; k < clicks.size() && clicks[k].frame == f; ++k) {
            if (clicks[k].down) s.checkpoints[k] = Ref<CheckpointObject>(pl->createCheckpoint());
        }
        while (next < clicks.size() && clicks[next].frame == f) {
            pl->handleButton(clicks[next].down, static_cast<int>(PlayerButton::Jump), true);
            ++next;
        }
        stepOnce(pl);
        if (pl->m_playerDied) return false;
    }
    return true;
}

// One trial: load the checkpoint before press `i`, move that press by `offset`
// whole frames, replay the recorded inputs that follow, and compare y.
// Sub-frame offsets need CBF's timing, which this version does not support.
bool runTrial(PlayLayer* pl, Session const& s, size_t i, double offset, double tolerance) {
    if (offset != std::floor(offset)) return false;
    auto const& cp = s.checkpoints[i];
    if (!cp.data()) return false;

    int64_t shift = static_cast<int64_t>(offset);
    int64_t start = s.macro.clicks[i].frame;

    // The shifted press plus every recorded input inside the horizon, in frame order.
    std::vector<std::pair<int64_t, bool>> events;
    for (size_t j = i; j < s.macro.clicks.size(); ++j) {
        if (s.macro.clicks[j].frame > start + kHorizon) break;
        int64_t f = s.macro.clicks[j].frame + (j == i ? shift : 0);
        events.push_back({ f, s.macro.clicks[j].down });
    }
    std::stable_sort(events.begin(), events.end(),
        [](auto const& a, auto const& b) { return a.first < b.first; });

    pl->loadFromCheckpoint(cp.data());

    std::vector<double> ys;
    ys.reserve(kHorizon + 1);
    size_t next = 0;
    for (int64_t step = 0; step <= kHorizon; ++step) {
        int64_t frame = start + step;
        while (next < events.size() && events[next].first <= frame) {
            pl->handleButton(events[next].second, static_cast<int>(PlayerButton::Jump), true);
            ++next;
        }
        stepOnce(pl);
        if (pl->m_playerDied) return false;
        ys.push_back(pl->m_player1->getPositionY());
    }
    return yTrackMatches(s.macro, i, tolerance, ys);
}

// Puts each press's window as a number at the press's position on the path.
void drawWindowLabels(PlayLayer* pl, Session const& s, std::vector<PressWindow> const& results) {
    if (auto old = pl->m_objectLayer->getChildByTag(kOverlayTag)) old->removeFromParent();

    auto layer = CCNode::create();
    layer->setTag(kOverlayTag);
    for (auto const& w : results) {
        auto it = std::lower_bound(s.macro.reference.begin(), s.macro.reference.end(), w.frame,
            [](YSample const& r, int64_t f) { return r.frame < f; });
        if (it == s.macro.reference.end() || it->frame != w.frame) continue;

        std::string text = fmt::format("{:g}", w.frames);
        auto label = CCLabelBMFont::create(text.c_str(), "bigFont.fnt");
        label->setScale(0.5f);
        label->setColor(w.frames < 3.0 ? kRed : kWhite);
        label->setPosition({ static_cast<float>(it->x), static_cast<float>(it->y) + 24.f });
        layer->addChild(label);
    }
    pl->m_objectLayer->addChild(layer);
}

} // namespace fw

CCMenuItemSpriteExtra* makeButton(char const* text, float width, float height,
                                  CCObject* target, SEL_MenuHandler sel) {
    auto node = CCNode::create();
    node->setContentSize({ width, height });

    auto bg = CCScale9Sprite::create("GJ_square01.png");
    bg->setContentSize({ width, height });
    bg->setColor({ 55, 55, 55 });
    bg->setPosition({ width / 2, height / 2 });
    node->addChild(bg);

    auto label = CCLabelBMFont::create(text, "bigFont.fnt");
    label->setColor(fw::kRed);
    label->setScale(std::min(0.5f, width * 0.9f / label->getContentSize().width));
    label->setPosition({ width / 2, height / 2 });
    node->addChild(label);

    auto button = CCMenuItemSpriteExtra::create(node, target, sel);
    button->setContentSize({ width, height });
    return button;
}

class FrameWindowPopup : public Popup {
    fw::Macro m_macro;
    bool m_hasMacro = false;
    CCLabelBMFont* m_status = nullptr;
    async::TaskHolder<Result<std::optional<std::filesystem::path>>> m_pickTask;

    bool initPopup() {
        if (!Popup::init(380.f, 480.f)) return false;

        auto size = m_mainLayer->getContentSize();
        float w = size.width;
        float h = size.height;

        auto title = CCLabelBMFont::create("Frame Window", "goldFont.fnt");
        title->setColor(fw::kRed);
        title->setPosition({ w / 2, h - 40.f });
        m_mainLayer->addChild(title);

        m_status = CCLabelBMFont::create("No recording yet", "chatFont.fnt");
        m_status->setPosition({ w / 2, h - 88.f });
        m_mainLayer->addChild(m_status);

        auto menu = CCMenu::create();
        menu->setPosition({ 0.f, 0.f });
        m_mainLayer->addChild(menu);

        float y = h - 130.f;
        addMenuButton(menu, "Start Recording", { w / 2, y }, menu_selector(FrameWindowPopup::onUnfinished)); y -= 50.f;
        addMenuButton(menu, "Run Analysis",    { w / 2, y }, menu_selector(FrameWindowPopup::onRunAnalysis)); y -= 50.f;
        addMenuButton(menu, "Playback",        { w / 2, y }, menu_selector(FrameWindowPopup::onPlayback));    y -= 50.f;
        addMenuButton(menu, "Save Macro",      { w / 2, y }, menu_selector(FrameWindowPopup::onUnfinished)); y -= 50.f;
        addMenuButton(menu, "Saved Macros",    { w / 2, y }, menu_selector(FrameWindowPopup::onUnfinished)); y -= 50.f;
        addMenuButton(menu, "Settings",        { w / 2, y }, menu_selector(FrameWindowPopup::onSettings));

        auto author = CCLabelBMFont::create("by Snoww", "chatFont.fnt");
        author->setOpacity(160);
        author->setAnchorPoint({ 0.f, 0.5f });
        author->setPosition({ 30.f, 30.f });
        m_mainLayer->addChild(author);

        auto importLabel = CCLabelBMFont::create("Import Macro", "chatFont.fnt");
        importLabel->setColor(fw::kBlue);
        auto importBtn = CCMenuItemSpriteExtra::create(importLabel, this, menu_selector(FrameWindowPopup::onImportMacro));
        importBtn->setPosition({ w - 80.f, 30.f });
        menu->addChild(importBtn);

        return true;
    }

    void addMenuButton(CCMenu* menu, char const* text, CCPoint pos, SEL_MenuHandler sel) {
        auto btn = makeButton(text, 320.f, 40.f, this, sel);
        btn->setPosition(pos);
        menu->addChild(btn);
    }

    void toast(std::string const& text, NotificationIcon icon) {
        Notification::create(text, icon)->show();
    }

    void onUnfinished(CCObject*) {
        toast("Not implemented in this version", NotificationIcon::Info);
    }

    void onSettings(CCObject*) {
        openSettingsPopup(Mod::get(), false);
    }

    void onRunAnalysis(CCObject*) {
        if (!m_hasMacro) {
            toast("Import a .gdr macro first", NotificationIcon::Warning);
            return;
        }
        auto* pl = PlayLayer::get();
        if (!pl) {
            toast("Open the replay's level first", NotificationIcon::Warning);
            return;
        }

        bool cbfWindows = Mod::get()->getSettingValue<bool>("cbf-windows");
        if (cbfWindows) {
            if (!Loader::get()->isModLoaded(fw::kCBFId)) {
                toast("CBF windows need Click Between Frames installed", NotificationIcon::Warning);
                return;
            }
            toast("CBF windows need the sub-frame trial, which is not written yet", NotificationIcon::Warning);
            return;
        }
        if (fw::cbfActive()) {
            toast("Turn CBF off (its soft toggle) before frame windows run", NotificationIcon::Warning);
            return;
        }

        auto started = std::chrono::steady_clock::now();
        double tolerance = Mod::get()->getSettingValue<double>("y-tolerance");

        fw::g_session.macro = m_macro;
        if (!fw::prepareSession(pl, fw::g_session)) {
            toast("The replay dies in this level. Check that the level matches.", NotificationIcon::Error);
            return;
        }

        size_t firstPress = 0;
        while (firstPress < fw::g_session.macro.clicks.size() && !fw::g_session.macro.clicks[firstPress].down) ++firstPress;
        if (firstPress >= fw::g_session.macro.clicks.size()) {
            toast("The replay has no presses", NotificationIcon::Warning);
            return;
        }
        if (!fw::runTrial(pl, fw::g_session, firstPress, 0.0, tolerance)) {
            toast("Baseline does not match the replay. Try a larger y tolerance.", NotificationIcon::Error);
            return;
        }

        fw::Trial trial = [pl, tolerance](size_t i, double offset) {
            return fw::runTrial(pl, fw::g_session, i, offset, tolerance);
        };
        auto results = fw::analyzeWindows(fw::g_session.macro, trial, fw::WindowMode::Frames);
        fw::drawWindowLabels(pl, fw::g_session, results);

        size_t totalTrials = 0;
        for (auto const& w : results) totalTrials += w.trials;
        double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();

        std::string text = fmt::format("{} presses | {} trials | {:.1f} s", results.size(), totalTrials, elapsed);
        m_status->setString(text.c_str());
    }

    void onPlayback(CCObject*) {
        if (!m_hasMacro) {
            toast("Import a .gdr macro first", NotificationIcon::Warning);
            return;
        }
        // TODO: real-time playback with the recorded inputs and the window labels.
        toast("Real-time playback is not written yet", NotificationIcon::Info);
    }

    void onImportMacro(CCObject*) {
        // Opens a file picker. Drag-and-drop still needs a file-drop listener.
        file::FilePickOptions options;
        options.filters.push_back({ "Geometry Dash replay", { "*.gdr" } });

        m_pickTask.spawn(
            file::pick(file::PickMode::OpenFile, options),
            [this](Result<std::optional<std::filesystem::path>> result) {
                if (result.isErr()) {
                    this->toast(result.unwrapErr(), NotificationIcon::Error);
                    return;
                }
                auto picked = result.unwrap();
                if (picked) this->loadMacro(*picked);  // empty means the user cancelled
            }
        );
    }

    void loadMacro(std::filesystem::path const& path) {
        auto parsed = fw::parseGDR(path);
        if (parsed.isErr()) {
            toast(parsed.unwrapErr(), NotificationIcon::Error);
            return;
        }
        m_macro = parsed.unwrap();
        m_hasMacro = true;

        std::string text = fmt::format("Loaded {}", m_macro.name);
        m_status->setString(text.c_str());
    }

public:
    static FrameWindowPopup* create() {
        auto ret = new FrameWindowPopup();
        if (ret->initPopup()) {
            ret->autorelease();
            return ret;
        }
        delete ret;
        return nullptr;
    }
};

void openFrameWindow() {
    auto scene = CCDirector::sharedDirector()->getRunningScene();
    if (!scene || scene->getChildByTag(fw::kMenuTag)) return;  // already open

    auto popup = FrameWindowPopup::create();
    if (!popup) return;
    popup->setTag(fw::kMenuTag);
    popup->show();
}

// Ctrl + Right Alt opens the menu.
class $modify(FWKeyboard, CCKeyboardDispatcher) {
    bool dispatchKeyboardMSG(enumKeyCodes key, bool down, bool repeat, double timestamp) {
        if (down && !repeat && key == static_cast<enumKeyCodes>(165) && this->getControlKeyPressed()) {
            openFrameWindow();
            return true;
        }
        return CCKeyboardDispatcher::dispatchKeyboardMSG(key, down, repeat, timestamp);
    }
};
