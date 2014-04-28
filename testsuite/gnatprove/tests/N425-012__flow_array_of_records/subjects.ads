package Subjects
with SPARK_Mode
is
   type CPU_Registers_Type is record
      A : Integer;
      B : Integer;
   end record;

   type Subject_State_Type is record
      Regs               : CPU_Registers_Type;
   end record;

   subtype Subject_Id_Type is Natural range 0 .. 4;

   type Subject_State_Array is array
     (Subject_Id_Type) of Subject_State_Type;

   Descriptors : Subject_State_Array;

   procedure Restore_State
     (Id   :     Subject_Id_Type;
      GPRs : out CPU_Registers_Type)
   with
      Global  => (Input  => Descriptors),
      Depends => (GPRs   =>  (Id, Descriptors));
private
end Subjects;
