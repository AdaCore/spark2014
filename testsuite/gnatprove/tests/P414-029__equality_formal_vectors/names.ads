package Names with
   SPARK_Mode
   --  Abstract_State => Name_Table,
   --  Initializes    => Name_Table
is

   type Name_Id is private;

   procedure Lookup (S : String;
                     N : out Name_Id)
   with --Global => (In_Out => Name_Table),
        Pre    => Invariant,
        Post   => Invariant;

   function To_String (N : Name_Id) return String
   with --Global => Name_Table,
        Pre    => Invariant;

   function Invariant return Boolean;
   --with Global => Name_Table;

private

   type Name_Id is new Natural;

end Names;
