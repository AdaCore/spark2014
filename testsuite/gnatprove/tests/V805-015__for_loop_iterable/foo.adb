with Ada.Text_IO; use Ada.Text_IO;

procedure Foo with SPARK_Mode is
   type Int_Range is record
      First, Last : Integer;
   end record with
     Predicate => Last < Integer'Last,
     Iterable => (First       => First,
                  Next        => Next,
                  Has_Element => Has_Element,
                  Element     => Element);

   function First (IR : Int_Range) return Integer is (IR.First);
   function Next (IR : Int_Range; N : Integer) return Integer is (N + 1) with
     Pre => Has_Element (IR, N);
   function Has_Element (IR : Int_Range; N : Integer) return Boolean is
     (N in IR.First ..IR.Last);
   function Element (IR : Int_Range; N : Integer) return Boolean is (True);

   procedure Test is
      IR : Int_Range := (1, 3);
   begin
      for I of IR loop
         Put (I'Img);
      end loop;
   end;
begin
   null;
end Foo;
