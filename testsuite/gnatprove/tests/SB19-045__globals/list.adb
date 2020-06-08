package body List with
  SPARK_Mode,
  Refined_State => (List => (Items, Used_Items))
is

   MAX_ITEMS : constant := 100;

   type T_Item (Used : Boolean := False) is record
      case Used is
         when True  => Value : Integer;
         when False => null;
      end case;
   end record;

   type T_Items is array (1 .. MAX_ITEMS) of T_Item;

   Items      : T_Items := (others => (Used => False));
   Used_Items : Integer := 0;

   ---------
   -- Add --
   ---------

   procedure Add
     (Value   : in  Integer;
      Success : out Boolean)
     with
       Refined_Global  => (In_Out => (Items, Used_Items))
--         Refined_Depends =>
--           (Items      =>+ (Used_Items, Value),
--            Used_Items =>+  null,
--            Success    =>  Used_Items)
   is
   begin

      if Used_Items = MAX_ITEMS then
         Success := False;
      else

         for I in Items'Range loop
            if not Items (I).Used then
               Items (I) := (Used => True, Value => Value);
               exit;
            end if;
         end loop;

         Used_Items := Used_Items + 1;
         Success    := True;

      end if;

   end Add;

end List;
