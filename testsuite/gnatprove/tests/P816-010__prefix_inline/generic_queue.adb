

package body Generic_Queue with SPARK_Mode => Off is

   --  Buffer Structure:
   --  | 0:X | 1:– | 2:– | 3:– |
   --    ^h    ^t
   --   head(h) points to oldest, tail(t) to next free,
   --   empty: t=h, full: t=h  => Flag Self.hasElements required




   procedure clear( Self : in out Buffer_Tag ) is
   begin
      Self.index_head := Index_Type'First;
      Self.index_tail := Index_Type'First;
      Self.hasElements := False;
   end clear;

   procedure fill( Self : in out Buffer_Tag ) is
   begin
      Self.index_tail := Self.index_head;
      Self.hasElements := True;
   end fill;


   procedure push_back( Self : in out Buffer_Tag; element : Element_Type) is
   begin
      if Self.Full then -- overflow
         Self.index_head := Index_Type'Succ( Self.index_head );
         if Self.Num_Overflows < Natural'Last then
            Self.Num_Overflows := Self.Num_Overflows + 1;
         end if;
      end if;
      Self.Buffer( Self.index_tail) := element;
      Self.index_tail := Index_Type'Succ( Self.index_tail );
      Self.hasElements := True;

      pragma Assert ( not Self.Empty );
   end push_back;


   procedure push_front( Self : in out Buffer_Tag; element : Element_Type ) is
   begin
      if Self.Full then -- overflow
         Self.index_tail := Index_Type'Pred( Self.index_tail );
         if Self.Num_Overflows < Natural'Last then
            Self.Num_Overflows := Self.Num_Overflows + 1;
         end if;
      end if;
      Self.index_head := Index_Type'Pred( Self.index_head );
      Self.Buffer( Self.index_head) := element;
      Self.hasElements := True;

      pragma Assert ( not Self.Empty );
   end push_front;


   procedure pop_front( Self : in out Buffer_Tag; element : out Element_Type) is
   begin
      pragma Assert (not Self.Empty);

      element := Self.Buffer( Self.index_head);
      Self.index_head := Index_Type'Succ( Self.index_head );
      if Self.index_tail = Self.index_head then
         Self.hasElements := False;
      end if;
   end pop_front;


   procedure pop_front( Self : in out Buffer_Tag; elements : out Element_Array ) is
   begin
      p_get(Self, elements);
      Self.index_head := Self.index_head + elements'Length;
      if Self.index_tail = Self.index_head then
         Self.hasElements := False;
      end if;
   end pop_front;

   --        entry pop_front_blocking( Self : in out Buffer_Tag; element : out Element_Type ) when Self.hasElements is
   --        begin
   --           element := Self.Buffer( Self.index_head);
   --           Self.index_head := Index_Type'Succ( Self.index_head );
   --           if Self.index_tail = Self.index_head then
   --              Self.hasElements := False;
   --           end if;
   --        end pop_front_blocking;

   procedure pop_back( Self : in out Buffer_Tag; element : out Element_Type) is
   begin
      pragma Assert (not Self.Empty);

      Self.index_tail := Index_Type'Pred( Self.index_tail );
      element := Self.Buffer( Self.index_tail);
      if Self.index_tail = Self.index_head then
         Self.hasElements := False;
      end if;
   end pop_back;

   procedure pop_all( Self : in out Buffer_Tag; elements : out Element_Array ) is
   begin
      p_get_all(Self, elements );
      Self.index_tail := 0;
      Self.index_head := 0;
      Self.hasElements := False;
   end pop_all;

   procedure get_all( Self : in Buffer_Tag; elements : out Element_Array ) is
   begin
      p_get_all(Self, elements );
   end get_all;

   procedure get_front( Self : in Buffer_Tag; element : out Element_Type ) is
   begin
      element := Self.Buffer(  Self.index_head );
   end get_front;

   procedure get_front( Self : in Buffer_Tag; elements : out Element_Array ) is
   begin
      p_get(Self, elements);
   end get_front;


   procedure get_back( Self : in Buffer_Tag; element : out Element_Type ) is
   begin
      pragma Assert (not Self.Empty);
      element := Self.Buffer(  Self.index_tail - 1 );
   end get_back;

   -- FIXME: remove this function?
--     function get_at( Self : in out Buffer_Tag; index : Index_Type ) return Element_Type is
--     begin
--        pragma Assert ( Self.index_head <= index and index < Self.index_tail );
--        return Self.Buffer(  index );
--     end get_at;

   procedure get_nth_first( Self : in Buffer_Tag; nth : Index_Type; element : out Element_Type) is
   begin
      pragma Assert ( Self.index_head <= Self.index_tail-1 - nth );
      element := Self.Buffer(  Self.index_tail-1 - nth );
   end get_nth_first;

   procedure get_nth_last( Self : in Buffer_Tag; nth : Index_Type; element : out Element_Type) is
   begin
      pragma Assert ( Self.index_head + nth <= Self.index_tail-1 );
      element := Self.Buffer(  Self.index_head + nth );
   end get_nth_last;

   function Length( Self : in Buffer_Tag ) return Length_Type is
   begin
      if Self.Full then
         return Length_Type'Last;
      else
         return Length_Type( Index_Type(Self.index_tail - Self.index_head) );
      end if;
   end Length;

   function Full( Self : in Buffer_Tag ) return Boolean is
   begin
      return (Self.index_tail = Self.index_head) and Self.hasElements;
   end Full;

   function hasElements( Self : in Buffer_Tag ) return Boolean is
   begin
      return Self.hasElements;
   end hasElements;


   function Empty( Self : in Buffer_Tag ) return Boolean is
   begin
      return not Self.hasElements;
   end Empty;

   function Overflows( Self : in Buffer_Tag ) return Natural is
   begin
      return Self.Num_Overflows;
   end Overflows;


   procedure p_get_all( Self : in Buffer_Tag; elements : out Element_Array ) is
   begin
      if not Self.Empty then
         if Self.index_head <= Self.index_tail-1 then  -- no wrap
            elements(1 .. Self.Length) := Element_Array( Self.Buffer( Self.index_head .. Self.index_tail-1) );
         else
            elements(1 .. Self.Length) := Element_Array( Self.Buffer( Self.index_head .. Index_Type'Last) & Self.Buffer( Index_Type'First .. Self.index_tail-1) );
         end if;
      else
         elements(1 .. 0) := Element_Array( Self.Buffer( 1 .. 0) ); -- empty
      end if;
   end p_get_all;

   procedure p_get( Self : in Buffer_Tag; elements : out Element_Array ) is
      delta_head : Index_Type;
   begin
      if not Self.Empty and elements'Length /= 0 then
         delta_head := Self.index_head + Index_Type(elements'Length - 1);
         if Self.index_head <= delta_head then  -- no wrap
            elements(1 .. elements'Length) := Element_Array( Self.Buffer( Self.index_head .. delta_head ) );
         else
            elements(1 .. elements'Length) := Element_Array( Self.Buffer( Self.index_head .. Index_Type'Last) & Self.Buffer( Index_Type'First .. delta_head ) );
         end if;
      else
         elements(1 .. 0) := Element_Array( Self.Buffer( 1 .. 0) ); -- empty
      end if;
   end p_get;



end Generic_Queue;
