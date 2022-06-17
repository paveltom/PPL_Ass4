export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}

// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    // optional initialization code
    return {
        get(key: string): Promise<T> {
            return sync().then((updTable: Table<T>) => updTable[key] != undefined ?  updTable[key] : Promise.reject(MISSING_KEY)).catch(() => Promise.reject(MISSING_KEY));
        },
        set(key: string, val: T): Promise<void> {
            return sync().then((updTable: Table<T>) => 
                    new Promise<void>(
                            (resolve, reject) => {
                                        if(updTable[key] != undefined) reject(); 
                                        const newTable:Table<any> = Object.assign(updTable, {[key] : val}); 
                                        //console.log(newTable);
                                        sync(newTable).then(()=>resolve());
                                    })
                                ).catch(() => Promise.reject(MISSING_KEY));
        },
        delete(key: string): Promise<void> {
            return sync().then((updTable: Table<T>) => 
                    new Promise<void>(
                            (resolve, reject) => {
                                        if(updTable[key] === undefined) reject(MISSING_KEY); 
                                        const newTable:Table<any> = 
                                            Object.keys(updTable).reduce((newTab : Table<any>, k: string) => {
                                                                                            if(k != key) { newTab = Object.assign(newTab, {[k] : updTable[k]}); } return newTab;}, {}); 
                                        //console.log(newTable);
                                        sync(newTable).then(()=>resolve());
                                    })
                                ).catch(() => Promise.reject(MISSING_KEY));
        }
    }
} 

// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    return Promise.all(
        keys.reduce((promList : Promise<T>[], key: string) => {
                                promList.push(store.get(key));
                                return promList; 
                            }, [])
    );
    

    // return Promise.all(keys.reduce((newList : T[], key: string) => {
    //                 store.get(key).then((res) => {newList.push(res); }).catch(() => {return Promise.reject(MISSING_KEY);})
    //                 return newList; }, []));


    // function getting(key: string) {
    //     return new Promise((resolve, reject) => {
    //         resolve(store.get(key));
    //     })
    // }

    // return Promise.all(keys.reduce((newList : T[], key: string) => {
    //     store.get(key).then((val : T) => {
    //         newList.push(val);
    //     }).catch();
    //     return newList;
    // }, []));

    // execute all promises here
                    
    //let out = [];
    // //console.log(keys);
    // for(let i = 0; i < keys.length; i++){

    //     out.push(new Promise((resolve, reject) => {}))

    //     const val = store.get(keys[i]);
    //     val.then((res) => {out.push(res)}).catch(() => {return Promise.reject(MISSING_KEY)});
    // }
    // // const val = store.get(keys[0]);
    // // val.then((res) => {console.log("curr res: ", res); out.push(res)}).catch(() => {return Promise.reject(MISSING_KEY)});
    // return Promise.all(out);


}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference) {
    async function deref(ref: Reference) {
        return Promise.reject('not implemented')
    }

    return deref(ref)
}

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        // TODO implement!
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        // TODO implement!
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    // optional initialization code

    let _table: Table<T> = await sync()

    const handleMutation = async (newTable: Table<T>) => {
        // TODO implement!
    }
    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            return handleMutation(null as any /* TODO */)
        },
        delete(key: string): Promise<void> {
            return handleMutation(null as any /* TODO */)
        },

        subscribe(observer: (table: Table<T>) => void): void {
            // TODO implement!
        }
    }
}