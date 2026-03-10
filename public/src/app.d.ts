
// See https://svelte.dev/docs/kit/types#app.d.ts
// for information about these interfaces
declare global {
    namespace App {
        // interface Error {}
        // interface Locals {}
        // interface PageData {}
        // interface PageState {}
        // interface Platform {}
    }
}

import 'unplugin-icons/types/svelte'

export interface Card {
    name: string,
    id: string,
    header?: string,
    locations: string[],
    answer: string,
    question: string,
}

module '$lib/cards.json' {
    const value: Card[];
    export default value;
}


export { };
