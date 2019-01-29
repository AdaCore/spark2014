package Problem_4 with SPARK_Mode => On is

   type List_Type is array (Integer range <>) of Integer;

   function Same_Elements (Left, Right : List_Type) return Boolean
     with
       Ghost,
       Pre => (Left'First = Right'First) and (Left'Last = Right'Last);

   procedure Swap (List : in out List_Type; I, J : Integer)
     with
       Pre  => (I in List'Range) and (J in List'Range),
       Post => (Same_Elements (List'Old, List));

end Problem_4;