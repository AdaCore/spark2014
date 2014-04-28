package body Subjects
with SPARK_Mode
is
   procedure Restore_State
     (Id   :     Subject_Id_Type;
      GPRs : out CPU_Registers_Type)
   is
   begin
      GPRs := Descriptors (Id).Regs;
   end Restore_State;
end Subjects;
