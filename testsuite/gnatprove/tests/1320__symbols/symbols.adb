package body Symbols
  with SPARK_Mode
is

   type Next_Type is range 1 .. 1001;
   subtype Index_Type is Next_Type range 1 .. 1000;

   type Storage_Type is array (Index_Type) of Symbol;

   type Holding_Type is record
      Memory : Storage_Type;
      Next   : Next_Type;
   end record
   with
     Predicate =>
       (for all I in Next .. Memory'Last => Holding_Type.Memory (I) = null);

   Storage : Holding_Type;

   function Space_Left return Boolean
   is (Storage.Next < Index_Type'Last);

   procedure Intern (S : String; Sym : out Symbol) is
   begin
      for I in Storage.Memory'Range loop
         if Storage.Memory (I) /= null and then S = Storage.Memory (I).all then
            Sym := Storage.Memory (I);
            return;
         end if;
      end loop;
      if Storage.Next = Next_Type'Last then
         raise Out_Of_Space;
      end if;
      declare
         Cur : Index_Type := Storage.Next;
      begin
         Storage.Next := Storage.Next + 1;
         Sym := new String'(S);
         Storage.Memory (Cur) := Sym;
      end;
   end Intern;
   pragma
     Annotate
       (Gnatprove,
        Intentional,
        "resource or memory leak might occur",
        "symbols indeed can't be deallocated by design");

end Symbols;
