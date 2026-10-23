//! Identical code folding: functions of one codegen unit whose Cranelift IR is the same compile
//! to the same machine code, so only the first of them is compiled and the others become
//! aliases of it (their symbols are pointed at its code when the object is written).
//!
//! Two functions are the same when their IR (`FunctionStencil`), the functions and data they
//! refer to (`user_named_funcs`) and the register allocator hint are equal: Cranelift's output
//! is a function of those alone, which is also what its incremental cache relies on. Monomorphic
//! copies of generic code often are (a `Vec<T>` method for two `T` of the same layout, closures
//! that capture the same shapes, drop glue of equally laid out types), as are the duplicated
//! cleanup and shim bodies.
//!
//! Rust promises no distinct addresses for distinct functions (LLVM's MergeFunctions, on by
//! default when optimizing, makes such aliases too), so this changes nothing a program may rely
//! on. An alias keeps its own symbol, linkage and visibility, only its address is the canonical
//! function's, so other codegen units and crates find it as before. Not done with debuginfo
//! (each function has its own description), for functions with `asm!`, nor for Mach-O (aliases
//! at one address break `.subsections_via_symbols`). In debug builds most functions are
//! exported (shared generics), so all functions defined in the codegen unit take part.

use std::hash::{Hash, Hasher};

use cranelift_codegen::ir::UserExternalName;
use rustc_data_structures::fx::{FxHashMap, FxHasher};

use crate::base::CodegenedFunction;
use crate::prelude::*;

fn stencil_hash(f: &CodegenedFunction) -> u64 {
    let mut hasher = FxHasher::default();
    f.func.stencil.hash(&mut hasher);
    f.regalloc.hash(&mut hasher);
    hasher.finish()
}

/// The function a reference names once folding is applied: the canonical copy of a folded one.
fn resolve(name: &UserExternalName, alias_of: &FxHashMap<u32, u32>) -> (u32, u32) {
    if name.namespace == 0
        && let Some(&canonical) = alias_of.get(&name.index)
    {
        return (0, canonical);
    }
    (name.namespace, name.index)
}

fn names_hash(f: &CodegenedFunction, alias_of: &FxHashMap<u32, u32>) -> u64 {
    let mut hasher = FxHasher::default();
    for name in f.func.params.user_named_funcs().values() {
        resolve(name, alias_of).hash(&mut hasher);
    }
    hasher.finish()
}

fn same(a: &CodegenedFunction, b: &CodegenedFunction, alias_of: &FxHashMap<u32, u32>) -> bool {
    let (na, nb) = (a.func.params.user_named_funcs(), b.func.params.user_named_funcs());
    a.regalloc == b.regalloc
        && na.len() == nb.len()
        && na.values().zip(nb.values()).all(|(x, y)| resolve(x, alias_of) == resolve(y, alias_of))
        && a.func.stencil == b.func.stencil
}

/// For each function, the function whose code it shares (`None`: compiled itself). `skip[i]`
/// leaves a function out (it isn't compiled at all); `may_fold` says which functions may become
/// aliases or be shared (those this codegen unit defines).
///
/// Repeated while it finds more: two functions that differ only in calling functions folded
/// into one another (drop glue of two equally laid out types) are the same too.
pub(crate) fn find(
    funcs: &[CodegenedFunction],
    skip: &[bool],
    may_fold: impl Fn(FuncId) -> bool,
) -> Vec<Option<FuncId>> {
    // Only functions that share their sizes with another one can be the same: hashing every
    // function's IR would cost more than the hashing of these few counts.
    let mut by_size: FxHashMap<(usize, usize, usize, usize, usize), u32> = FxHashMap::default();
    let size = |f: &CodegenedFunction| {
        let func = &f.func;
        (
            func.dfg.num_insts(),
            func.dfg.num_blocks(),
            func.dfg.num_values(),
            func.sized_stack_slots.len(),
            func.params.user_named_funcs().len(),
        )
    };
    let mut candidates: Vec<usize> = (0..funcs.len())
        .filter(|&i| {
            !skip.get(i).copied().unwrap_or(false)
                && !funcs[i].inline_hints.has_inline_asm
                && may_fold(funcs[i].func_id)
        })
        .collect();
    for &i in &candidates {
        *by_size.entry(size(&funcs[i])).or_default() += 1;
    }
    candidates.retain(|&i| by_size[&size(&funcs[i])] > 1);
    let stencil_hashes: Vec<u64> = candidates.iter().map(|&i| stencil_hash(&funcs[i])).collect();
    // Folded function id -> canonical function id (always one that is compiled).
    let mut alias_of: FxHashMap<u32, u32> = FxHashMap::default();
    let mut canonical: Vec<Option<usize>> = vec![None; funcs.len()];
    for _round in 0..8 {
        let mut first: FxHashMap<(u64, u64), Vec<usize>> = FxHashMap::default();
        let mut found = vec![];
        for (&i, &stencil_hash) in candidates.iter().zip(&stencil_hashes) {
            if canonical[i].is_some() {
                continue;
            }
            let f = &funcs[i];
            let firsts = first.entry((stencil_hash, names_hash(f, &alias_of))).or_default();
            if let Some(&j) = firsts.iter().find(|&&j| same(&funcs[j], f, &alias_of)) {
                found.push((i, j));
            } else {
                firsts.push(i);
            }
        }
        if found.is_empty() {
            break;
        }
        for (i, j) in found {
            canonical[i] = Some(j);
        }
        // A canonical function of an earlier round may itself have been folded now.
        alias_of.clear();
        for i in 0..funcs.len() {
            if let Some(mut j) = canonical[i] {
                while let Some(k) = canonical[j] {
                    j = k;
                }
                canonical[i] = Some(j);
                alias_of.insert(funcs[i].func_id.as_u32(), funcs[j].func_id.as_u32());
            }
        }
    }
    canonical.into_iter().map(|c| c.map(|j| funcs[j].func_id)).collect()
}
