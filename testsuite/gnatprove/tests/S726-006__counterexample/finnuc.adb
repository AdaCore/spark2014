--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator (dev)
--  Command line arguments: -l ada
--    --pre-process-xmi
--    --clean finnuc.xmi

pragma Style_Checks ("M999");  --  ignore long lines
pragma Warnings (GNATprove, Off, "Unused assignment",
                 Reason => "Assignment is used");
with finnuc_types; use finnuc_types;
with Interfaces; use Interfaces;
with Ada.Text_IO; use Ada.Text_IO;
package body finnuc
with Refined_State =>
  (State =>
     (Unit_Delay_memory,
      Memory_memory,
      Memory_memory_1))
is
   Unit_Delay_memory : Boolean ;
   Memory_memory : Boolean ;
   Memory_memory_1 : Boolean ;

   function Boolean_To_Unsigned_8 (B : Boolean) return Unsigned_8 is
     (if B then 1 else 0);

   procedure init is
   begin
      --  Block 'finnuc/setAB/Select B/Unit Delay'
      Unit_Delay_memory := False;
      --  End Block 'finnuc/setAB/Select B/Unit Delay'

      --  Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Memory'
      Memory_memory := True;
      --  End Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Memory'

      --  Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Memory'
      Memory_memory_1 := False;
   end init;

   procedure comp
     (SetA : Boolean;
      SetB : Boolean;
      C : Boolean;
      A : out Boolean;
      B : out Boolean;
      OldA : out Boolean)
   is

      Demux_out1 : Boolean;
      Demux_out2 : Boolean;
      Demux_out1_1 : Boolean;
      Demux_out2_1 : Boolean;
      Logical_Operator1_out1 : Boolean;
      Mux_out1 : Boolean_Array_3 := (others => False);
      Mux_out1_1 : Boolean_Array_3 := (others => False);
      Logic_table : Boolean_Array_8_2 :=
        (1 =>(1 => False, 2 => True),
         2 =>(1 => True, 2 => False),
         3 =>(1 => False, 2 => True),
         4 =>(1 => False, 2 => True),
         5 =>(1 => True, 2 => False),
         6 =>(1 => True, 2 => False),
         7 =>(1 => False, 2 => False),
         8 =>(1 => False, 2 => False));
      Logic_index : Unsigned_8;
      Logic_table_1 : Boolean_Array_8_2 :=
        (1 =>
           (1 => False, 2 => True), 2 =>
             (1 => True, 2 => False), 3 =>
             (1 => False, 2 => True), 4 =>
             (1 => False, 2 => True), 5 =>
             (1 => True, 2 => False), 6 =>
             (1 => True, 2 => False), 7 =>
             (1 => False, 2 => False), 8 =>
             (1 => False, 2 => False));
      Logic_index_1 : Unsigned_8;
   begin
      --  Block 'finnuc/setAB/Select B/Logical Operator'
      --  Block 'finnuc/setAB/C'
      --  Block 'finnuc/setAB/Select B/Unit Delay'
      --  Block 'finnuc/setAB/SetB'
      --  Block 'finnuc/setAB/Select B/Logical Operator1'
      Logical_Operator1_out1 := ((Unit_Delay_memory)
                                 and then (C))
        or else (SetB);
      --  End Block 'finnuc/setAB/Select B/Logical Operator1'
      --  End Block 'finnuc/setAB/SetB'
      --  End Block 'finnuc/setAB/Select B/Unit Delay'
      --  End Block 'finnuc/setAB/C'
      --  End Block 'finnuc/setAB/Select B/Logical Operator'

      --  Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Memory'
      --  Block 'finnuc/setAB/SetA'
      --  Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Mux'
      Mux_out1 (1) := SetA;
      Mux_out1 (2) := Logical_Operator1_out1;
      Mux_out1 (3) := Memory_memory;
      --  End Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Mux'
      --  End Block 'finnuc/setAB/SetA'
      --  End Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Memory'

      --  Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Logic'
      Logic_index := (((Boolean_To_Unsigned_8 (Mux_out1 (1))) * (4)) + ((Boolean_To_Unsigned_8 (Mux_out1 (2))) * (2))) + ((Boolean_To_Unsigned_8 (Mux_out1 (3))) * (1));
      --  End Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Logic'

      --  Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Demux'
      Demux_out1 := Logic_table ((Integer (Logic_index)) + (1), 1);
      Demux_out2 := Logic_table ((Integer (Logic_index)) + (1), 2);

      --  End Block 'finnuc/setAB/Select A/SRFlipFlopLogic/Demux'

      --  Block 'finnuc/setAB/A'
      A := Demux_out1;
      --  End Block 'finnuc/setAB/A'

      --  Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Memory'
      --  Block 'finnuc/setAB/Select B/Logical Operator2'
      --  Block 'finnuc/setAB/SetA'
      --  Block 'finnuc/setAB/C'
      --  Block 'finnuc/setAB/Select B/Logical Operator3'
      --  Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Mux'
      Mux_out1_1 (1) := Logical_Operator1_out1;
      Mux_out1_1 (2) := (SetA)
        and then (not (C));
      Mux_out1_1 (3) := Memory_memory_1;
      --  End Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Mux'
      --  End Block 'finnuc/setAB/Select B/Logical Operator3'
      --  End Block 'finnuc/setAB/C'
      --  End Block 'finnuc/setAB/SetA'
      --  End Block 'finnuc/setAB/Select B/Logical Operator2'
      --  End Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Memory'

      --  Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Logic'
      Logic_index_1 := (((Boolean_To_Unsigned_8 (Mux_out1_1 (1))) * (4)) + ((Boolean_To_Unsigned_8 (Mux_out1_1 (2))) * (2))) + ((Boolean_To_Unsigned_8 (Mux_out1_1 (3))) * (1));
      --  End Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Logic'

      --  Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Demux'
      Demux_out1_1 := Logic_table_1 ((Integer (Logic_index_1)) + (1), 1);
      Demux_out2_1 := Logic_table_1 ((Integer (Logic_index_1)) + (1), 2);

      --  End Block 'finnuc/setAB/Select B/SRFlipFlopLogic/Demux'

      --  Block 'finnuc/setAB/B'
      B := Demux_out1_1;
      --  End Block 'finnuc/setAB/B'

      --  output the value of a from previous step for
      --  contract
      OldA := Unit_Delay_memory;

      --  update 'finnuc/setAB/Select B/Unit Delay'
      Unit_Delay_memory := Demux_out1;
      --  End update 'finnuc/setAB/Select B/Unit Delay'

      --  update 'finnuc/setAB/Select A/SRFlipFlopLogic/Memory'
      Memory_memory := Demux_out1;
      --  End update 'finnuc/setAB/Select A/SRFlipFlopLogic/Memory'

      --  update 'finnuc/setAB/Select B/SRFlipFlopLogic/Memory'
      Memory_memory_1 := Demux_out1_1;
      --  End update 'finnuc/setAB/Select B/SRFlipFlopLogic/Memory'


   end comp;

end finnuc;
--  @EOF
