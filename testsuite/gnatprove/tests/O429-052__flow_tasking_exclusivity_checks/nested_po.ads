package nested_po is

   protected type PT is
      entry Dummy;
   end;

   type Inner is
      record
         PO : PT;
      end record;
   pragma Volatile (Inner);

   type Outer is
      record
         Inner_Rec : Inner;
      end record;
   pragma Volatile (Outer);

   Outer_Rec : Outer;

   task type TT;

   T : TT;

end;
