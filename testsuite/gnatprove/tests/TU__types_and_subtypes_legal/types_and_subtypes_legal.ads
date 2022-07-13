package Types_And_Subtypes_Legal
  with SPARK_Mode
is
   type Node is private;

   function Get_Data (N : Node) return Integer
     with Global   => null,
          Annotate => (GNATprove, Always_Return);

   function "=" (X, Y : Node) return Boolean is (Get_Data (X) = Get_Data (Y));

   function Get_Next (N : Node) return Node
     with Global   => null,
          Annotate => (GNATprove, Always_Return);
private
   pragma SPARK_Mode (Off);

   type Node is record
      Data : Integer := 0;
      Next : access Node := null;
   end record;

   Null_Node : constant Node := Node'(Data => 0, Next => null);
end Types_And_Subtypes_Legal;
