procedure Ho_Specialization with SPARK_Mode is

   --  Non-specializable calls in pre-condition prevent automatic
   --  instantation of lemma with higher-order specialization

   V : Integer := 0;
   function Read_V return Integer is (V);
   function Call (F : not null access function return Integer;
                  G : not null access function return Integer) return Integer
   is (if F.all < 0 then G.all else F.all)
     with Annotate => (GNATprove, Higher_Order_Specialization);
   procedure Bad_Lemma (F : not null access function return Integer)
     with
       Always_Terminates,
       Ghost,
       Pre => Call (F, Read_V'Access) = 0,
       Post => True,
       Annotate => (GNATprove, Automatic_Instantiation),
       Annotate => (GNATprove, Higher_Order_Specialization);
   procedure Bad_Lemma (F : not null access function return Integer) is null;

   --  Passing an access-to-function parameter to a function without higher-order
   --  specialization is not allowed in the contract of a specializable function.

   function Non_Specialized_Call
     (F : not null access function return Integer) return Integer is (F.all);
   function Bad_Call (F : not null access function return Integer) return Integer
     with Post => Bad_Call'Result = Non_Specialized_Call (F),
       Annotate => (GNATprove, Higher_Order_Specialization);
   function Bad_Call (F : not null access function return Integer) return Integer
     is (Non_Specialized_Call (F));

begin
   null;
end Ho_Specialization;
