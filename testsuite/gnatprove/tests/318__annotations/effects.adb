procedure Effects with SPARK_Mode is

   function F1 return Integer is (1);

   procedure P1 with Import, Global => null, Ghost,
     No_Return,
     Annotate => (GNATprove, Automatic_Instantiation);

   function F2 return Integer is (1);

   procedure P2 with Import, Global => null, Ghost,
     Exceptional_Cases => (others => True),
     Annotate => (GNATprove, Automatic_Instantiation);

   procedure P3 with Import, Global => null, Ghost,
     No_Return,
     Annotate => (GNATprove, Higher_Order_Specialization);

   procedure P4 with Import, Global => null, Ghost,
     Exceptional_Cases => (others => True),
     Annotate => (GNATprove, Higher_Order_Specialization);

begin
   null;
end Effects;
