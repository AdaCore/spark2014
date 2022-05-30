procedure Test with
  SPARK_Mode
is
   type Ptr is access Integer;

   procedure Foo (X : in out Ptr) --  OK
   is
      Z : constant Ptr := X;
   begin
      if Z.all > 10 then
         X := Z;
         goto Test;
      elsif Z.all > 100 then
         X := Z;
         goto Test;
      elsif Z.all > 1000 then
         null;
      else
         X := Z;
         goto Test;
      end if;

      Z.all := Z.all * 2;

      X := Z;
      <<Test>>
   end Foo;

   procedure Foo_2 (X : in out Ptr) --  moved value for "X" on return
   is
      Z : constant Ptr := X;
   begin
      if Z.all > 10 then
         goto Test;
      elsif Z.all > 100 then
         X := Z;
         goto Test;
      elsif Z.all > 1000 then
         null;
      else
         X := Z;
         goto Test;
      end if;

      Z.all := Z.all * 2;

      X := Z;
      <<Test>>
   end Foo_2;

   procedure Foo_3 (X : in out Ptr) --  moved value for "X" on return
   is
      Z : constant Ptr := X;
   begin
      if Z.all > 10 then
         X := Z;
         goto Test;
      elsif Z.all > 100 then
         goto Test;
      elsif Z.all > 1000 then
         null;
      else
         X := Z;
         goto Test;
      end if;

      Z.all := Z.all * 2;

      X := Z;
      <<Test>>
   end Foo_3;

   procedure Foo_4 (X : in out Ptr) --  moved value for "X" on return
   is
      Z : constant Ptr := X;
   begin
      if Z.all > 10 then
         X := Z;
         goto Test;
      elsif Z.all > 100 then
         X := Z;
         goto Test;
      elsif Z.all > 1000 then
         null;
      else
         goto Test;
      end if;

      Z.all := Z.all * 2;

      X := Z;
      <<Test>>
   end Foo_4;

   procedure Foo_5 (X : in out Ptr) --  moved value for "X" on return
   is
      Z : constant Ptr := X;
   begin
      if Z.all > 10 then
         X := Z;
         goto Test;
      elsif Z.all > 100 then
         X := Z;
         goto Test;
      elsif Z.all > 1000 then
         null;
      else
         X := Z;
         goto Test;
      end if;

      Z.all := Z.all * 2;

      <<Test>>
   end Foo_5;
begin
   null;
end Test;
