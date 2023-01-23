procedure Test_Rec with SPARK_Mode is

   --  Recursive call to a function annotated with Higher_Order_Specialization

   function F (G : not null access function (X : Integer) return Integer)
               return Integer
     with Pre => True,
     Post => F(G) = 0,
     Annotate => (GNATprove, Higher_Order_Specialization);

   function F (G : not null access function (X : Integer) return Integer)
     return Integer
     is (0);

   --  Mutually recursive call to a function annotated with Higher_Order_Specialization

   function F1 (G : not null access function (X : Integer) return Integer)
               return Integer
     with Pre => True,
     Post => F2(G) = 0,
     Annotate => (GNATprove, Higher_Order_Specialization);

   function F2 (G : not null access function (X : Integer) return Integer)
               return Integer
     with Pre => True,
     Post => F1(G) = 0,
     Annotate => (GNATprove, Higher_Order_Specialization);

   function F1 (G : not null access function (X : Integer) return Integer)
     return Integer
     is (0);

   function F2 (G : not null access function (X : Integer) return Integer)
     return Integer
     is (0);

   --  Mutually recursive call to a not function annotated with
   --  Higher_Order_Specialization. This should be rejected.

   function F3 (G : not null access function (X : Integer) return Integer)
               return Integer
     with Pre => True,
     Post => F4(G) = 0;

   function F4 (G : not null access function (X : Integer) return Integer)
               return Integer
     with Pre => True,
     Post => F3(G) = 0,
     Annotate => (GNATprove, Higher_Order_Specialization);

   function F3 (G : not null access function (X : Integer) return Integer)
     return Integer
     is (0);

   function F4 (G : not null access function (X : Integer) return Integer)
     return Integer
     is (0);

begin
   null;
end Test_Rec;
