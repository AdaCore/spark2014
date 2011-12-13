with Counter;

package body Vectors is

   procedure Set_Id (Container : in out Vector)
   --# derives Container from Container;
   is
      --# hide Set_Id;  --  Hide side-effect on global Counter
   begin
      Container.Id := Counter.Bump_Counter;
   end Set_Id;

   procedure Bump_Sig (Container : in out Vector)
   --# derives Container from Container;
   is
   begin
      Container.Sig := Container.Sig + 1;
   end Bump_Sig;

   procedure Init_Vector (Container : out Vector) is
   begin
      Container := Vector'(0, 1, Elements_Array'(others => 0), 0);
      Set_Id (Container);
   end Init_Vector;

   function Length (Container : Vector) return Count_Type is
   begin
      return (Container.Last_Index - Index_Type'First) + 1;
   end Length;

   function First_Cursor (Container : Vector) return Cursor is
      Position : Cursor;
   begin
      if Length (Container) > 0 then
         Position := Cursor'(Container_Id  => Container.Id,
                             Container_Sig => Container.Sig,
                             Last_Index    => Container.Last_Index,
                             Index         => Index_Type'First);
      else
         Position := No_Element;
      end if;
      return Position;
   end First_Cursor;

   function Last_Cursor (Container : Vector) return Cursor is
      Position : Cursor;
   begin
      if Length (Container) > 0 then
         Position := Cursor'(Container_Id  => Container.Id,
                             Container_Sig => Container.Sig,
                             Last_Index    => Container.Last_Index,
                             Index         => Container.Last_Index);
      else
         Position := No_Element;
      end if;
      return Position;
   end Last_Cursor;

   function Associated
     (Container : Vector;
      Position  : Cursor) return Boolean
   --# return Container.Id = Position.Container_Id
   --#        and then Container.Sig = Position.Container_Sig
   --#        and then Length (Container) > 0
   --#        and then Position.Last_Index = Container.Last_Index
   --#        and then Position.Index <= Position.Last_Index;
   is
   begin
      return Container.Id = Position.Container_Id
        and then Container.Sig = Position.Container_Sig;
   end Associated;

   function Element_At
     (Container : Vector;
      Position  : Cursor) return Element_Type is
   begin
      return Container.Elements (Position.Index);
   end Element_At;

   procedure Next (Position : in out Cursor) is
   begin
      if Position.Index < Position.Last_Index then
         Position.Index := Position.Index + 1;
      else
         Position := No_Element;
      end if;
   end Next;

   procedure Replace_Element
     (Container : in out Vector;
      Position  : Cursor;
      New_Item  : Element_Type) is
   begin
      Container.Elements (Position.Index) := New_Item;
   end Replace_Element;

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      New_Item  : Element_Type) is
   begin
      for J in reverse Index_Type range Before.Index .. Container.Last_Index
      loop
         Container.Elements (J + 1) := Container.Elements (J);
      end loop;
      Container.Elements (Before.Index) := New_Item;
      Container.Last_Index := Container.Last_Index + 1;
      Bump_Sig (Container);
   end Insert;

   procedure Delete
     (Container : in out Vector;
      Position  : Cursor) is
   begin
      for J in Index_Type range Position.Index .. Container.Last_Index
      loop
         Container.Elements (J) := Container.Elements (J + 1);
      end loop;
      Container.Last_Index := Container.Last_Index - 1;
      Bump_Sig (Container);
   end Delete;

end Vectors;
