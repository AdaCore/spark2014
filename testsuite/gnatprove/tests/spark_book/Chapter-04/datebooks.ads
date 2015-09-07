---------------------------------------------------------------------------
-- FILE    : datebooks.ads
-- SUBJECT : Package providing a simple datebook type.
-- AUTHOR  : (C) Copyright 2013 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Dates;
use type Dates.Datetime;

package Datebooks is

   type Datebook is private;

   Maximum_Number_Of_Events : constant := 64;
   subtype Event_Count_Type is Natural range 0 .. Maximum_Number_Of_Events;

   type Status_Type is (Success, Description_Too_Long, Insufficient_Space, No_Event);

   -- Initializes the datebook.
   procedure Initialize(Book : out Datebook)
   with
     Depends => (Book => null);

   -- Adds an event to the datebook.
   --   Fails with Description_Too_Long if the description string is too large to store.
   --   Fails with Insufficient_Space if the datebook is full.
   procedure Add_Event(Book : in out Datebook; Description : in String; Date : in Dates.Datetime; Status : out Status_Type)
   with
     Depends => ( Book => (Book, Description, Date), Status => (Book, Description) );

   -- Removes all events before the given date. This procedure can't fail.
   procedure Purge_Events_Before(Book : in out Datebook; Date : in Dates.Datetime)
   with
     Depends => (Book =>+ Date);

   -- Returns the date associated with the earliest event.
   --   Fails with No_Event if the datebook is empty.
   procedure Get_Earliest_Event_Date(Book : in Datebook; Date : out Dates.Datetime; Status : out Status_Type)
   with
     Depends => ( (Date, Status) => Book );

   -- Returns the description on the event at the given date.
   --   Fails with No_Event if there are no event on the given date.
   --   Fails with Description_Too_Long if the Description string isn't large enough to receive the description text.
   procedure Get_Event(Book : in Datebook; Date : in Dates.Datetime; Description : out String; Status : out Status_Type)
   with
     Depends => ( (Description, Status) => (Book, Date, Description) );

   -- Returns the first date associated with an event after the Current_Date.
   --   Fails with No_Event if there is no later event.
   procedure Get_Next_Event_Date
     (Book : in Datebook; Current_Date : in Dates.Datetime; Next_Date : out Dates.Datetime; Status : out Status_Type)
   with
     Depends => ( (Next_Date, Status) => (Book, Current_Date) );

   -- Returns the number of events currently in the datebook.
   function Event_Count(Book : in Datebook) return Event_Count_Type;

private

   -- Provide an appropriate type definition.
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
   type Datebook is array(Event_Index_Type) of Event_Record;

end Datebooks;
