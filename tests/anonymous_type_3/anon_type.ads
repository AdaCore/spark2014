------------------------------------------------------------------------------
--  Test the anonymous type as component_list in the record type
--

package Anon_Type
is
   type Months is (Jan, Feb, Mar, Apr, May, June,
                   July, Aug, Sept, Oct, Nov, Dec);

   type Date is record
      Day        : Integer range 1 .. 31;
      Month      : Months;
      Year       : Integer range 1 .. 4000;
      Day_String : String(1 .. 6);
   end record;

   type Nothing is tagged record
      null;
   end record;

   ToDay1, ToDay2, ToDay3 : Date;

   procedure Date_Format(ToDay1 , ToDay2 , ToDay3 : out Date);

end Anon_Type;

