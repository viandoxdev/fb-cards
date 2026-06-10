const STORAGE_KEY = 'flashbang-settings';

type SettingsShape = {
    fontSize: number;
    useSansFont: boolean;
};

const defaults: SettingsShape = {
    fontSize: 20,
    useSansFont: false,
};

function load(): SettingsShape {
    if (typeof localStorage === 'undefined') return { ...defaults };
    try {
        const raw = localStorage.getItem(STORAGE_KEY);
        if (!raw) return { ...defaults };
        const parsed = JSON.parse(raw) as Partial<SettingsShape>;
        return {
            fontSize:
                typeof parsed.fontSize === 'number'
                    ? parsed.fontSize
                    : defaults.fontSize,
            useSansFont:
                typeof parsed.useSansFont === 'boolean'
                    ? parsed.useSansFont
                    : defaults.useSansFont,
        };
    } catch {
        return { ...defaults };
    }
}

export const settings = $state<SettingsShape>(load());

export function resetSettings() {
    settings.fontSize = defaults.fontSize;
    settings.useSansFont = defaults.useSansFont;
}

if (typeof window !== 'undefined') {
    $effect.root(() => {
        $effect(() => {
            const snapshot: SettingsShape = {
                fontSize: settings.fontSize,
                useSansFont: settings.useSansFont,
            };
            try {
                localStorage.setItem(STORAGE_KEY, JSON.stringify(snapshot));
            } catch {
                // quota / disabled storage — ignore
            }
        });
    });
}
