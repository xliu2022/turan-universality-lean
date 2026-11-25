/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TuranUniversality.Selector.RootedImage

/-! # Source witnesses for each rooted edge shape -/

@[expose] public section

namespace TuranUniversality.Selector

open Weighted

variable {X Roots : Type*} [DecidableEq X] [DecidableEq Roots]

@[simp] theorem two_root_disjSum (r s : Roots) (x : X) :
    ({r, s} : Finset Roots).disjSum {x} = {Sum.inl r, Sum.inl s, Sum.inr x} := by
  ext v
  cases v <;> simp

@[simp] theorem one_root_disjSum (r : Roots) (x y : X) :
    ({r} : Finset Roots).disjSum {x, y} = {Sum.inl r, Sum.inr x, Sum.inr y} := by
  ext v
  cases v <;> simp

@[simp] theorem zero_root_disjSum (x y z : X) :
    (∅ : Finset Roots).disjSum {x, y, z} = {Sum.inr x, Sum.inr y, Sum.inr z} := by
  ext v
  cases v <;> simp

theorem two_root_edge_witness (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) (r s : Roots) (x : X)
    (he : ({r, s}, {x}) ∈ (rootedImage A ρ hρ).edges) :
    ∃ y z, ρ y = some r ∧ ρ z = some s ∧ ρ x = none ∧ {y, z, x} ∈ A.edges := by
  have hg := (split_edge_mem_iff (rootedImage A ρ hρ) {r, s} {x}).mp he
  simp only [rootedImage_toRGraph, two_root_disjSum] at hg
  obtain ⟨y, hy⟩ := rootedGraph_root_exists A ρ hρ hg (by simp : Sum.inl r ∈ _)
  obtain ⟨z, hz⟩ := rootedGraph_root_exists A ρ hρ hg (by simp : Sum.inl s ∈ _)
  have hx := rootedGraph_data_none A ρ hρ hg (by simp : Sum.inr x ∈ _)
  refine ⟨y, z, hy, hz, hx, ?_⟩
  apply (rootedGraph_reflect_triple A ρ hρ y z x).mp
  simpa [rootedVertex, hy, hz, hx] using hg

theorem one_root_edge_witness (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) (r : Roots) (x y : X)
    (he : ({r}, {x, y}) ∈ (rootedImage A ρ hρ).edges) :
    ∃ z, ρ z = some r ∧ ρ x = none ∧ ρ y = none ∧ {z, x, y} ∈ A.edges := by
  have hg := (split_edge_mem_iff (rootedImage A ρ hρ) {r} {x, y}).mp he
  simp only [rootedImage_toRGraph, one_root_disjSum] at hg
  obtain ⟨z, hz⟩ := rootedGraph_root_exists A ρ hρ hg (by simp : Sum.inl r ∈ _)
  have hx := rootedGraph_data_none A ρ hρ hg (by simp : Sum.inr x ∈ _)
  have hy := rootedGraph_data_none A ρ hρ hg (by simp : Sum.inr y ∈ _)
  refine ⟨z, hz, hx, hy, ?_⟩
  apply (rootedGraph_reflect_triple A ρ hρ z x y).mp
  simpa [rootedVertex, hz, hx, hy] using hg

theorem data_edge_witness (A : RGraph X 3) (ρ : X → Option Roots)
    (hρ : ∀ x y r, ρ x = some r → ρ y = some r → x = y) (x y z : X)
    (he : (∅, {x, y, z}) ∈ (rootedImage A ρ hρ).edges) :
    ρ x = none ∧ ρ y = none ∧ ρ z = none ∧ {x, y, z} ∈ A.edges := by
  have hg := (split_edge_mem_iff (rootedImage A ρ hρ) ∅ {x, y, z}).mp he
  simp only [rootedImage_toRGraph, zero_root_disjSum] at hg
  have hx := rootedGraph_data_none A ρ hρ hg (by simp : Sum.inr x ∈ _)
  have hy := rootedGraph_data_none A ρ hρ hg (by simp : Sum.inr y ∈ _)
  have hz := rootedGraph_data_none A ρ hρ hg (by simp : Sum.inr z ∈ _)
  refine ⟨hx, hy, hz, ?_⟩
  apply (rootedGraph_reflect_triple A ρ hρ x y z).mp
  simpa [rootedVertex, hx, hy, hz] using hg

end TuranUniversality.Selector
