package body Memregions
with
   SPARK_Mode,
   Refined_State => (State => (Memory, Validity))
is
   subtype Array_Index is Positive range 1 .. 20;

   type Memory_Array is array (Array_Index) of Memory_Type;

   Validity : Boolean := False;
   Memory   : Memory_Array;

   function Is_Valid return Boolean is (Validity);

   procedure Init
   is
   begin
      for M of Memory loop
         M.Index := 1;
      end loop;

      Validity := True;
   end Init;

   function Get_Index (Idx : Positive) return Memory_Type
   with
      Refined_Global => (Input => Memory, Proof_In => Validity)
   is
      Res : Memory_Type := (Index => 0);
   begin
      for M of Memory loop
         if M.Index = Idx then
            Res := M;
         end if;
      end loop;

      return Res;
   end Get_Index;

   procedure Memory_Has_Index (Idx : Natural)
   with
      Refined_Global => (Input => Memory, Proof_In => Validity)
   is
   begin
      for M of Memory loop
         if M.Index = Idx then
            Process (M => M);
         end if;
      end loop;
   end Memory_Has_Index;

   procedure Default_Process (M : Memory_Type)
   with
      SPARK_Mode => Off
   is
   begin
      null;
   end Default_Process;

end Memregions;
