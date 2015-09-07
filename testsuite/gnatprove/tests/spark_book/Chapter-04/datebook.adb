---------------------------------------------------------------------------
-- FILE    : datebook.adb
-- SUBJECT : Package providing a simple datebook of events.
-- AUTHOR  : (C) Copyright 2014 by Peter C. Chapin and John McCormick
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Datebook
with
   Refined_State => (State => Event_Array)
is

   Maximum_Description_Length : constant := 128;
   subtype Description_Index_Type is Positive range 1 .. Maximum_Description_Length;
   subtype Description_Count_Type is Natural  range 0 .. Maximum_Description_Length;
   subtype Description_Type is String(Description_Index_Type);

   -- Each Event_Record handles exactly one datebook entry.
   type Event_Record is
      record
         Description_Text : Description_Type;        -- An array to hold the description.
         Description_Size : Description_Count_Type;  -- The number of characters in Description_Text that are used.
         Date             : Dates.Datetime;          -- The date associated with this event.
         Is_Used          : Boolean;                 -- True if this event record is meaningful.
      end record;

   subtype Event_Index_Type is Positive range 1 .. Maximum_Number_Of_Events;
   type Event_Array_Type is array(Event_Index_Type) of Event_Record;

   -- The events are stored here in no particular order.
   Event_Array : Event_Array_Type;


   procedure Initialize
      with
         Refined_Global  => (Output => Event_Array),
         Refined_Depends => (Event_Array => null)
   is
   begin
      Event_Array := Event_Array_Type'
        (others => Event_Record'(Description_Text => Description_Type'(others => ' '),
                                 Description_Size => 0,
                                 Date             => Dates.Default_Datetime,
                                 Is_Used          => False));
   end Initialize;


   -- Adds an event to the datebook.
   --   Fails with Description_Too_Long if the description string is too large to store.
   --   Fails with Insufficient_Space if the datebook is full.
   procedure Add_Event (Description : in  String;
                        Date        : in  Dates.Datetime;
                        Status      : out Status_Type)
      with
         Refined_Global  => (In_Out => Event_Array),
         Refined_Depends => (Event_Array =>+ (Description, Date),
                             Status      => (Description, Event_Array))
   is
      Found     : Boolean;    -- Is there an available slot?
      Available : Event_Index_Type := Event_Index_Type'First; -- Location
   begin
      -- If the given description won't fit there is no point continuing.
      if Description'Length > Maximum_Description_Length then
         Status := Description_Too_Long;
      else
         -- Search for a free slot in the event array.
         Found := False;
         for Index in Event_Index_Type loop
            if not Event_Array (Index).Is_Used then
               Available := Index;
               Found := True;
               exit; -- We found a available slot in the array
            end if;
         end loop;

         if not Found then
            -- If there is no free slot return an error.
            Status := Insufficient_Space;
         else
            -- Otherwise fill in the free slot with the incoming information.
            -- Need to pad the description with blanks.
            Event_Array (Available).Description_Text := Description &
                 (1 .. Maximum_Description_Length - Description'Length => ' ');
            Event_Array (Available).Description_Size := Description'Length;
            Event_Array (Available).Date    := Date;
            Event_Array (Available).Is_Used := True;
            Status := Success;
         end if;
      end if;
   end Add_Event;


   -- Removes all events before the given date. This procedure can't fail.
   procedure Purge_Events_Before(Date : in Dates.Datetime)
      with
         Refined_Global  => (In_Out => Event_Array),
         Refined_Depends => (Event_Array =>+ Date)
   is
   begin
      for Index in Event_Index_Type loop
         if Dates.Is_Before (Event_Array(Index).Date, Date) then
            Event_Array (Index).Is_Used := False;
         end if;
      end loop;
   end Purge_Events_Before;


   -- Returns the date associated with the earliest event.
   --   Fails with No_Event if the datebook is empty.
   procedure Get_Earliest_Event_Date(Date : out Dates.Datetime; Status : out Status_Type)
      with
         Refined_Global => (Input => Event_Array),
         Refined_Depends => ((Date, Status) => Event_Array)
   is
   begin
      Status := No_Event;
      Date   := Dates.Default_Datetime;  -- A value to use in case there is No_Event.

      for Index in Event_Index_Type loop
         -- We found a real event...
         if Event_Array (Index).Is_Used then

            -- If this is the first event found, save it unconditionally.
            if Status = No_Event then
               Date   := Event_Array (Index).Date;
               Status := Success;
            else
               -- Otherwise save this event only if it is earlier than our best so far.
               if Dates.Is_Before (Event_Array (Index).Date, Date) then
                  Date := Event_Array (Index).Date;
               end if;
            end if;
         end if;
      end loop;
   end Get_Earliest_Event_Date;


   -- Returns the description on the event at the given date.
   --   Fails with No_Event if there are no event on the given date.
   --   Fails with Description_Too_Long if the Description string isn't large enough to receive
   --   the description text.
   procedure Get_Event (Date        : in Dates.Datetime;
                        Description : out String;
                        Status      : out Status_Type)
      with
         Refined_Global => (Input => Event_Array),
         Refined_Depends => ((Description, Status) => (Event_Array, Date, Description))
   is
      Index : Event_Index_Type;
   begin
      Status      := No_Event;
      Description := (others => ' ');

      Index := Event_Index_Type'First;
      loop
         -- Is this item in the event array the one we are looking for?
         if Event_Array (Index).Date = Date then
            if Description'Length < Event_Array (Index).Description_Size then
               Status := Description_Too_Long;
            else
               for J in Description_Count_Type range
                 1 .. Event_Array(Index).Description_Size loop

                  pragma Loop_Invariant
                    (Event_Array (Index).Description_Size <= Description'Length and then
                     Index = Index'Loop_Entry and then
                     (J - 1) < Description'Length);

                  Description(Description'First + (J - 1)) :=
                    Event_Array(Index).Description_Text(J);
               end loop;
               Status := Success;
            end if;
            exit;
         end if;

         -- If not, then advance to the next item.
         exit when Index = Event_Index_Type'Last;
         Index := Index + 1;
      end loop;
   end Get_Event;


   -- Returns the first date associated with an event after the Current_Date.
   --   Fails with No_Event if there is no later event.
   procedure Get_Next_Event_Date (Current_Date : in Dates.Datetime;
                                  Next_Date    : out Dates.Datetime;
                                  Status       : out Status_Type)
      with
         Refined_Global => (Input => Event_Array),
         Refined_Depends => ((Next_Date, Status) => (Event_Array, Current_Date))
   is

      -- Returns True if D1 is after D2; False otherwise.
      function Is_After(D1 : Dates.Datetime; D2 : Dates.Datetime) return Boolean is
      begin
         return not Dates.Is_Before(D1, D2) and D1 /= D2;
      end Is_After;

   begin
      Status    := No_Event;
      Next_Date := Dates.Default_Datetime;  -- A value to use in case there is No_Event.

      for Index in Event_Index_Type loop
         if Event_Array(Index).Is_Used and then
           Is_After(Event_Array(Index).Date, Current_Date) then

            Next_Date := Event_Array(Index).Date;
            Status := Success;
            exit;
         end if;
      end loop;
   end Get_Next_Event_Date;


   -- Returns the number of events currently in the datebook.
   function Event_Count return Event_Count_Type
      with
         Refined_Global => (Input => Event_Array)
   is
      Count : Event_Count_Type := 0;
   begin
      for Index in Event_Index_Type loop
         pragma Loop_Invariant(Count < Index);

         if Event_Array(Index).Is_Used then
            Count := Count + 1;
         end if;
      end loop;
      return Count;
   end Event_Count;

end Datebook;
