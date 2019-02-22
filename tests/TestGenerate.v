Require Import OrderedTypeEx Generate.

From Coq Require Import Ascii String.

Generate OrderedType ascii.
Generate OrderedType string.

Open Scope string.

Eval vm_compute in "cat" =?= "dog".

Require Import Sets.

Eval vm_compute in
    cardinal {"dog"; {"cat"; {"dog"; {"hamster"; {}}}}}.