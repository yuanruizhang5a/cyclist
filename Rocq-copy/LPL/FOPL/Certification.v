(** * FOPL uses the shared checker-reflection theorem unchanged. *)
From CyclistRocq.LPL.FOPL Require Import Signature Rules.
From CyclistRocq.LPL Require Import Certification.

Module MakeCertification (S : SIGNATURE) (Kernel : KERNEL S).
Module Export Checked := CyclistRocq.LPL.Certification.MakeCertification
  Kernel.Core.Pr.Sem.Syn.Language Kernel.Core.Pr.Sem.Syn.Shared
  Kernel.Core.Pr.Sem.Shared Kernel.Core.Pr.Shared Kernel.SharedKernel.
Module Export Sem := Kernel.Core.Pr.Sem.
Module Export Syn := Sem.Syn.
Module Export P := Kernel.P.
Export Kernel.
End MakeCertification.
