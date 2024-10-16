package body Ext_2 with SPARK_Mode is

   --  Early usage in body is OK

   package Q is

      function F (X : T) return Integer;

      function G (X : Integer) return T;

   end Q;

   type T is tagged record
      C : Integer;
   end record;

   package body P is

      function F (X : T) return Integer is
        (X.C);

      function G (X : Integer) return T is
        (T'(C => X));
   end P;

   package body Q is

      function F (X : T) return Integer is
        (X.C);

      function G (X : Integer) return T is
        (T'(C => X));
   end Q;

end Ext_2;
