//! Trace is a pretty niche data structure which is used when lowering a CST
//! into HIR.
//!
//! Lowering process calculates two bits of information:
//! * the lowered syntax itself
//! * a mapping between lowered syntax and original syntax
//!
//! Due to the way salsa works, the mapping is usually hot lava, as it contains
//! absolute offsets. The `Trace` structure (inspired, at least in name, by
//! Kotlin's `BindingTrace`) allows use the same code to compute both
//! projections.
use la_arena::{Arena, ArenaMap, Idx, RawIdx};

pub(crate) struct Trace<T, V> {
    data: Option<Arena<T>>,
    value: Option<ArenaMap<Idx<T>, V>>,
    len: u32,
}

impl<T, V> Trace<T, V> {
    #[allow(dead_code)]
    pub(crate) fn new_for_data() -> Trace<T, V> {
        Trace { data: Some(Arena::default()), value: None, len: 0 }
    }

    pub(crate) fn new_for_value() -> Trace<T, V> {
        Trace { data: None, value: Some(ArenaMap::default()), len: 0 }
    }

    pub(crate) fn alloc(&mut self, value: impl FnOnce() -> V, data: impl FnOnce() -> T) -> Idx<T> {
        let id = if let Some(arena) = &mut self.data {
            arena.alloc(data())
        } else {
            let id = Idx::<T>::from_raw(RawIdx::from(self.len));
            self.len += 1;
            id
        };

        if let Some(map) = &mut self.value {
            map.insert(id, value());
        }
        id
    }

    #[allow(dead_code)]
    pub(crate) fn into_data(mut self) -> Arena<T> {
        self.data.take().unwrap()
    }

    pub(crate) fn into_value(mut self) -> ArenaMap<Idx<T>, V> {
        self.value.take().unwrap()
    }
}

pub(crate) struct TraceMap<T, V> {
    data: Option<ArenaMap<Idx<T>, T>>,
    value: Option<ArenaMap<Idx<T>, V>>,
    len: u32,
}

impl<T, V> TraceMap<T, V> {
    pub(crate) fn new_for_data() -> Self {
        Self { data: Some(ArenaMap::default()), value: None, len: 0 }
    }

    pub(crate) fn new_for_value() -> Self {
        Self { data: None, value: Some(ArenaMap::default()), len: 0 }
    }

    pub(crate) fn alloc(
        &mut self,
        value: impl FnOnce() -> V,
        data: impl FnOnce() -> (Idx<T>, T),
    ) -> Idx<T> {
        let id = if let Some(arena) = &mut self.data {
            let (id, t) = data();
            arena.insert(id, t);
            id
        } else {
            let id = Idx::<T>::from_raw(RawIdx::from(self.len));
            self.len += 1;
            id
        };

        if let Some(map) = &mut self.value {
            map.insert(id, value());
        }
        id
    }

    pub(crate) fn into_data(mut self) -> ArenaMap<Idx<T>, T> {
        self.data.take().unwrap()
    }

    pub(crate) fn into_value(mut self) -> ArenaMap<Idx<T>, V> {
        self.value.take().unwrap()
    }
}
