import Lake
open Lake DSL

package "Hoare" where
  -- add package configuration options here

lean_lib «Hoare» where
  -- add library configuration options here

@[default_target]
lean_exe "hoare" where
  root := `Main
