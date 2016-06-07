package Declare_Iterable with SPARK_Mode is
   type Container is private with
     Iterable => (Has_Element => Has_Element,
                  Next        => Next,
                  First       => First,
                  Element     => Element);

   type Cursor is range 0 .. 100;
   subtype Valid_Cursor is Cursor range 1 .. 100;

   type Nat_Array is array (Valid_Cursor) of Natural;

   function Has_Element (X : Container; C : Cursor) return Boolean;
   function Next (X : Container; C : Cursor) return Cursor with
     Pre => Has_Element (X, C);
   function First (X : Container) return Cursor;
   function Element (X : Container; C : Cursor) return Natural with
     Pre => Has_Element (X, C);

   function From_Nat_Array (A : Nat_Array) return Container;
   function To_Nat_Array (X : Container) return Nat_Array;

private
   type Container is record
      Content : Nat_Array;
   end record;

   function Has_Element (X : Container; C : Cursor) return Boolean is
      (C in Valid_Cursor);
   function Next (X : Container; C : Cursor) return Cursor is
      (if C = 100 then 0 else C + 1);
   function First (X : Container) return Cursor is (1);
   function Element (X : Container; C : Cursor) return Natural is
     (X.Content (C));

   function From_Nat_Array (A : Nat_Array) return Container is (Content => A);
   function To_Nat_Array (X : Container) return Nat_Array is (X.Content);
end Declare_Iterable;
