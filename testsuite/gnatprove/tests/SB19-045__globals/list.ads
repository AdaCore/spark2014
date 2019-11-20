package List with
  SPARK_Mode,
  Abstract_State => List,
  Initializes    => List
is

   procedure Add
     (Value   : in  Integer;
      Success : out Boolean)
     with
       Global  => (In_Out  => List),
       Depends => (Success => List, List => Value);

   --  GNATprove runs without any problems when
   --
   --     List => Value
   --
   --  is replaced by
   --
   --     List =>+ Value

end List;
