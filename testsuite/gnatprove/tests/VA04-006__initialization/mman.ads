package Mman
  with
  SPARK_Mode,
  Abstract_State => Shared_Memory_Control,
  Initializes =>
    (Shared_Memory_Control,
     Shm_Revocation_Ledger)
is

   type Shm_Revocation_Ledger_T is new Integer;
   Shm_Revocation_Ledger : Shm_Revocation_Ledger_T := 0;

   procedure Proc;
end Mman;
