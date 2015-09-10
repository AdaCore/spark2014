---------------------------------------------------------------------------
-- FILE    : data_storage.ads
-- SUBJECT : Specification of an abstract database interface package for Thumper.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------

with Ada.Calendar;
with Serial_Generator;
with Timestamp_Messages;

use Ada.Calendar;
use Serial_Generator;
use Timestamp_Messages;

-- TODO: This package should be a SPARK boundary variable package!
package Data_Storage is

   subtype Count_Type is Natural;
   subtype Index_Type is Positive range 1 .. Count_Type'Last;
   type Timestamp_Array is array(Index_Type range <>) of Timestamp;

   -- Does what is necessary to get the storage ready for use. If this package is initialized
   -- more than once, the additional initializations are ignored. However, they are counted.
   --
   procedure Initialize;

   -- Does what is necessary to put the storage to bed. The actual shutdown occurs only when
   -- this procedure is called the same number of times as Initialized was called. For example,
   -- if Initialize was called five times, this procedure must also be called five times to
   -- actually shut down the storage.
   --
   procedure Shutdown;

   -- Returns the number of time stamps in storage.
   function Timestamp_Count return Count_Type;

   -- Adds the give time stamp to the storage.
   procedure Timestamp_Store(Stamp : in Timestamp);

   -- Returns all time stamps in storage with the given serial number. The returned array might
   -- be empty. If the returned array contains more than one element the server has violated an
   -- important rule: it should never generate multiple time stamps with the same serial number.
   --
   function Timestamp_Retrieve(Serial_Number : Serial_Number_Type) return Timestamp_Array;

   -- Returns all time stamps in storage between the given start and stop times (inclusive). An
   -- empty array might be returned. If Stop comes before Start an empty array will definitely
   -- be returned.
   --
   function Timestamp_Retrieve(Start : Time; Stop : Time) return Timestamp_Array;

end Data_Storage;
