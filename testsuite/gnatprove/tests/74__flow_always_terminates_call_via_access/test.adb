procedure Test with SPARK_Mode
is

   type Func_Acc is access function (I : Integer) return Integer;
   type Proc_Acc is access procedure (I : out Integer);

   function No_Call (I : Integer) return Integer;     --@TERMINATION:PASS

   function Call (I : Integer) return Integer;        --@TERMINATION:PASS

   Glob_No_Call : Func_Acc := No_Call'Access;         --@TERMINATION:NONE
   Glob_Call : Func_Acc := Call'Access;               --@TERMINATION:FAIL

   function No_Call (I : Integer) return Integer is
   begin
      return I;
   end No_Call;

   function Call (I : Integer) return Integer is
      F : Func_Acc := No_Call'Access;                 --@TERMINATION:NONE
   begin
      return F.all (I);                               --@TERMINATION:NONE
   end Call;

   function NOK return Boolean is
      F : Func_Acc := Call'Access;                    --@TERMINATION:FAIL
   begin
      return F.all (1) = 1;                           --@TERMINATION:NONE
   end NOK;

   procedure POK (I : out Integer) with Always_Terminates is --@TERMINATION:PASS
      F : Func_Acc := No_Call'Access;                        --@TERMINATION:NONE
   begin
      I := F.all (1);                                        --@TERMINATION:NONE
   end POK;

   procedure PNOK (I : out Integer) with Always_Terminates is
      F : Func_Acc := Call'Access;                    --@TERMINATION:FAIL
   begin
      I := F.all (1);                                 --@TERMINATION:NONE
   end PNOK;

   procedure P_Test_With_Annot (I : out Integer) with Always_Terminates is
   begin
      POK (I);  --@TERMINATION:NONE
      PNOK (I); --@TERMINATION:NONE
   end P_Test_With_Annot;

   procedure InferOK (I : out Integer) with Pre => True is
      F : Func_Acc := No_Call'Access; --@TERMINATION:NONE
   begin
      I := F.all (1);                 --@TERMINATION:NONE
   end InferOK;

   procedure InferNOK (I : out Integer) with Pre => True is
      F : Func_Acc := Call'Access; --@TERMINATION:FAIL
   begin
      I := F.all (1);              --@TERMINATION:NONE
   end InferNOK;

   procedure P_Test_With_Infer (I : out Integer) with Always_Terminates is
   begin
      InferOK (I);  --@TERMINATION:NONE
      InferNOK (I); --@TERMINATION:NONE
   end P_Test_With_Infer;

   procedure P_Proc_Access (I : out Integer) with Always_Terminates is
      P : Proc_Acc := POK'Access; --@TERMINATION:NONE
   begin
      P.all (I); --@TERMINATION:FAIL
   end P_Proc_Access;

   procedure P_Global_OK (I : out Integer) with Always_Terminates is
   begin
      I := Glob_No_Call.all (1); --@TERMINATION:NONE
      I := Glob_Call.all (1);    --@TERMINATION:NONE
   end P_Global_OK;

   procedure P_Ghost_Terminates is
      P : Proc_Acc := InferNOK'Access with Ghost;
      No_Call_Acc : Func_Acc := No_Call'Access with Ghost; --@TERMINATION:NONE
      Call_Acc : Func_Acc := Call'Access with Ghost;       --@TERMINATION:FAIL
      I, J, K : Integer with Ghost;
   begin
      P.all (I);                 --@TERMINATION:FAIL
      J := No_Call_Acc.all (1);  --@TERMINATION:NONE
      K := Call_Acc.all (1);     --@TERMINATION:NONE
   end P_Ghost_Terminates;
begin
   null;
end Test;
