package body P is

   protected body PO is

      procedure Proc is
         type T is record
            C : Integer := PO.X;
            --  In protected procedures and entries the enclosing protected
            --  object acts as an implicit formal parameter of mode IN OUT, so
            --  the default initialization of this component should be rejected
            --  as depending on variable input.
            --
            --  This is just like the non-protected Proc procedure below.
         end record;

         function Nested_Func return Integer is
            type T is record
               C : Integer := PO.X;
            end record;
         begin
            return 0;
         end;
      begin
         null;
      end;

      function Fun return Integer is
         type T is record
            C : Integer := PO.X;
            --  But in protected function the enclosing protected object acts
            --  as an implicit formal parameter of mode IN, so the default
            --  initialization of this component should be accepted.
            --
            --  This is just like the non-protected Fun function below.
         end record;

         procedure Nested_Proc is
            type T is record
               C : Integer := PO.X;
            end record;
         begin
            null;
         end;
      begin
         return 0;
      end;

   end PO;

   function Fun (X : Integer) return Integer is
      type T is record
         C : Integer := X; -- OK
      end record;
   begin
      return X;
   end;

   procedure Proc (X : in out Integer) is
      type T is record
         C : Integer := X; -- Error
      end record;
   begin
      null;
   end;

   --  This is just like the PO above, but for a non-single protected unit

   protected body PT is

      procedure Proc is
         type T is record
            C : Integer := PT.X; -- Error
         end record;
      begin
         null;
      end;

      function Fun return Integer is
         type T is record
            C : Integer := PT.X; -- OK
         end record;
      begin
         return 0;
      end;

   end PT;

end P;
