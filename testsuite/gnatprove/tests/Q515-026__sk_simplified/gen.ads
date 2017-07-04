package Gen
  with SPARK_Mode => On
is

   type Word64 is mod 2**64;

   type Segment_Type is record
      Selector      : Word64;
   end record;

   type Subject_State_Type is record
      Regs               : Word64;
      Exit_Reason        : Word64;
      Exit_Qualification : Word64;
      Guest_Phys_Addr    : Word64;
      Instruction_Len    : Word64;
      RIP                : Word64;
      RSP                : Word64;
      CR0                : Word64;
      SHADOW_CR0         : Word64;
      LDTR               : Segment_Type;
   end record;

   function Get_Val (E : Subject_State_Type) return Integer
   is (0)
     with
     Post => False;


end Gen;
