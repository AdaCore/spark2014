---------------------------------------------------------------------------
-- FILE    : datebooks.adb
-- SUBJECT : Package providing a simple datebook type.
-- AUTHOR  : (C) Copyright 2013 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Datebooks is

   procedure Initialize(Book : out Datebook) is
   begin
      Book := Datebook'
        (others => Event_Record'(Description_Text => Description_Type'(others => ' '),
                                 Description_Size => 0,
                                 Date             => Dates.Default_Datetime,
                                 Is_Used          => False));
   end Initialize;


   procedure Add_Event(Book : in out Datebook; Description : in String; Date : in Dates.Datetime; Status : out Status_Type) is
      type Find_Result_Record is
         record
            Fresh_Index : Event_Index_Type;
            Found_Slot  : Boolean;
         end record;

      Find_Result : Find_Result_Record;
   begin
      Find_Result := Find_Result_Record'(Fresh_Index => 1, Found_Slot => False);

      -- If the given description won't fit there is no point continuing.
      if Description'Length > Maximum_Description_Length then
         Status := Description_Too_Long;
      else
         -- Search for a free slot in the event array.
         for I in Event_Index_Type loop
            pragma Loop_Invariant(Description'Length <= Maximum_Description_Length);

            if not Book(I).Is_Used then
               Find_Result := Find_Result_Record'(Fresh_Index => I, Found_Slot => True);
               exit;
            end if;
         end loop;

         -- If there is no free slot return an error.
         if not Find_Result.Found_Slot then
            Status := Insufficient_Space;
         else
            -- Otherwise fill in the free slot with the incoming information.
            Book(Find_Result.Fresh_Index).Description_Text := Description_Type'(others => ' ');
            for I in Positive range Description'Range loop
               pragma Loop_Invariant(Find_Result.Fresh_Index in Event_Index_Type           and
                                     Description'Length      <= Maximum_Description_Length and
                                     I - Description'First   <  Maximum_Description_Length);

               Book(Find_Result.Fresh_Index).Description_Text(1 + (I - Description'First)) := Description(I);
            end loop;
            Book(Find_Result.Fresh_Index).Description_Size := Description'Length;
            Book(Find_Result.Fresh_Index).Date             := Date;
            Book(Find_Result.Fresh_Index).Is_Used          := True;
            Status := Success;
         end if;
      end if;
   end Add_Event;


   procedure Purge_Events_Before(Book : in out Datebook; Date : in Dates.Datetime) is
   begin
      for I in Event_Index_Type loop
         if Dates.Is_Before(Book(I).Date, Date) then
            Book(I).Is_Used := False;
         end if;
      end loop;
   end Purge_Events_Before;


   procedure Get_Earliest_Event_Date(Book : in Datebook; Date : out Dates.Datetime; Status : out Status_Type) is
   begin
      Status := No_Event;
      Date   := Dates.Default_Datetime;  -- A value to use in case there is No_Event.

      for I in Event_Index_Type loop
         -- We found a real event...
         if Book(I).Is_Used then

            -- If this is the first event found, save it unconditionally.
            if Status = No_Event then
               Date   := Book(I).Date;
               Status := Success;
            else
               -- Otherwise save this event only if it is earlier than our best so far.
               if Dates.Is_Before(Book(I).Date, Date) then
                  Date := Book(I).Date;
               end if;
            end if;
         end if;
      end loop;
   end Get_Earliest_Event_Date;


   procedure Get_Event(Book : in Datebook; Date : in Dates.Datetime; Description : out String; Status : out Status_Type) is
      I : Event_Index_Type;
   begin
      Status      := No_Event;
      Description := (others => ' ');

      I := Event_Index_Type'First;
      loop
         -- Is this item in the event array the one we are looking for?
         if Book(I).Date = Date then
            if Description'Length < Book(I).Description_Size then
               Status := Description_Too_Long;
            else
               for J in Description_Count_Type range 1 .. Book(I).Description_Size loop
                  pragma Loop_Invariant
                    (Book(I).Description_Size <= Description'Length and
                     I = I'Loop_Entry and
                     J - 1 < Description'Length);

                  Description(Description'First + (J - 1)) := Book(I).Description_Text(J);
               end loop;
               Status := Success;
            end if;
            exit;
         end if;

         -- If not, then advance to the next item.
         exit when I = Event_Index_Type'Last;
         I := I + 1;
      end loop;
   end Get_Event;


   procedure Get_Next_Event_Date
     (Book : Datebook; Current_Date : in Dates.Datetime; Next_Date : out Dates.Datetime; Status : out Status_Type) is

      -- Returns True if D1 is after D2; False otherwise.
      function Is_After(D1 : Dates.Datetime; D2 : Dates.Datetime) return Boolean is
      begin
         return not Dates.Is_Before(D1, D2) and D1 /= D2;
      end Is_After;

   begin
      Status    := No_Event;
      Next_Date := Dates.Default_Datetime;  -- A value to use in case there is No_Event.

      for I in Event_Index_Type loop
         if Book(I).Is_Used and then Is_After(Book(I).Date, Current_Date) then
            Next_Date := Book(I).Date;
            Status    := Success;
            exit;
         end if;
      end loop;
   end Get_Next_Event_Date;


   function Event_Count(Book : in Datebook) return Event_Count_Type is
      Count : Event_Count_Type := 0;
   begin
      for I in Event_Index_Type loop
         pragma Loop_Invariant(Count < I);

         if Book(I).Is_Used then
            Count := Count + 1;
         end if;
      end loop;
      return Count;
   end Event_Count;

end Datebooks;
