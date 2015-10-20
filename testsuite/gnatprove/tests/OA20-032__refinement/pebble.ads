pragma Style_Checks (Off);

with Interfaces.C; use Interfaces.C;
with Strings_Interface;
with System;
with Interfaces.C.Extensions;

package Pebble is

   subtype Opaque_Ptr is System.Address;
   Null_Opaque_Ptr : constant Opaque_Ptr := System.Null_Address;

   type Window is private;
   Null_Window : constant Window;

   type U_Bool is new Interfaces.C.Extensions.bool;

   subtype Int8_T is signed_char;
   subtype Int16_T is short;
   subtype Int32_T is int;
   subtype Int64_T is long;
   subtype Uint8_T is unsigned_char;
   subtype Uint16_T is unsigned_short;
   subtype Uint32_T is unsigned;
   subtype Uint64_T is unsigned_long;
   subtype Size_T is unsigned_long;
   subtype Time_T is System.Address;

   function Gnat_Malloc (Size : Interfaces.C.size_t) return System.Address;
   pragma Export (C, Gnat_Malloc, "__gnat_malloc");

   procedure Gnat_Free (Ptr : System.Address);
   pragma Export (C, Gnat_Free, "__gnat_free");

   function Rand return int;
   pragma Import (C, Rand, "rand");

   procedure Srand (Arg1 : unsigned);
   pragma Import (C, Srand, "srand");

   function Rand_R (Arg1 : access unsigned) return int;
   pragma Import (C, Rand_R, "rand_r");


   Trig_Max_Ratio : constant := 16#ffff#;  --  pebble.h:254

   Trig_Max_Angle : constant := 16#10000#;  --  pebble.h:259


   Uuid_Size : constant := 16;  --  pebble.h:842

   Uuid_String_Buffer_Length : constant := (32 + 4 + 2 + 1);  --  pebble.h:873



   --//! Constant to indicate infinite play count.
   --//! Can be passed to \ref animation_set_play_count() to repeat indefinitely.
   --//! @note This can be returned by \ref animation_get_play_count().

   Animation_Normalized_Min : constant := 0;  --  pebble.h:4290

   Animation_Normalized_Max : constant := 65535;  --  pebble.h:4293

   Action_Bar_Width : constant := 30;  --  pebble.h:6012

   Num_Action_Bar_Items : constant := 3;  --  pebble.h:6015

   Status_Bar_Layer_Height : constant := 16;  --  pebble.h:6171

   Tz_Len : constant := 6;  --  pebble.h:6595

   type Buttonid is
     (Button_Id_Back,
      Button_Id_Up,
      Button_Id_Select,
      Button_Id_Down,
      Num_Buttons);
   pragma Convention (C, Buttonid);  -- pebble.h:167

   function I18n_Get_System_Locale
     return Strings_Interface.Chars_Ptr;  -- pebble.h:185
   pragma Import (C, I18n_Get_System_Locale, "i18n_get_system_locale");


   package Uuid is
      type Uuid_T is record
         Byte0  : aliased Uint8_T;
         Byte1  : aliased Uint8_T;
         Byte2  : aliased Uint8_T;
         Byte3  : aliased Uint8_T;
         Byte4  : aliased Uint8_T;
         Byte5  : aliased Uint8_T;
         Byte6  : aliased Uint8_T;
         Byte7  : aliased Uint8_T;
         Byte8  : aliased Uint8_T;
         Byte9  : aliased Uint8_T;
         Byte10 : aliased Uint8_T;
         Byte11 : aliased Uint8_T;
         Byte12 : aliased Uint8_T;
         Byte13 : aliased Uint8_T;
         Byte14 : aliased Uint8_T;
         Byte15 : aliased Uint8_T;
      end record;
      pragma Convention (C_Pass_By_Copy, Uuid_T);  -- pebble.h:840

      function Equal
        (Arg1 : access constant Uuid_T;
         Arg2 : access constant Uuid_T) return U_Bool;  -- pebble.h:864
      pragma Import (C, Equal, "uuid_equal");

      procedure To_String
        (Arg1 : access constant Uuid_T;
         Arg2 : Strings_Interface.Chars_Ptr);  -- pebble.h:870
      pragma Import (C, To_String, "uuid_to_string");

   end Uuid;

   procedure App_Event_Loop;  -- pebble.h:2011
   pragma Import (C, App_Event_Loop, "app_event_loop");

   type Sniffinterval is (Sniff_Interval_Normal, Sniff_Interval_Reduced);
   pragma Convention (C, Sniffinterval);  -- pebble.h:2104

   procedure App_Comm_Set_Sniff_Interval
     (Arg1 : Sniffinterval);  -- pebble.h:2110
   pragma Import
     (C,
      App_Comm_Set_Sniff_Interval,
      "app_comm_set_sniff_interval");

   function App_Comm_Get_Sniff_Interval return Sniffinterval;  -- pebble.h:2114
   pragma Import
     (C,
      App_Comm_Get_Sniff_Interval,
      "app_comm_get_sniff_interval");

   function Heap_Bytes_Free return Size_T;  -- pebble.h:2159
   pragma Import (C, Heap_Bytes_Free, "heap_bytes_free");

   function Heap_Bytes_Used return Size_T;  -- pebble.h:2163
   pragma Import (C, Heap_Bytes_Used, "heap_bytes_used");


   type Applaunchreason is
     (App_Launch_System,
      App_Launch_User,
      App_Launch_Phone,
      App_Launch_Wakeup,
      App_Launch_Worker,
      App_Launch_Quick_Launch,
      App_Launch_Timeline_Action);
   pragma Convention (C, Applaunchreason);  -- pebble.h:2410

   function Launch_Reason return Applaunchreason;  -- pebble.h:2414
   pragma Import (C, Launch_Reason, "launch_reason");

   function Launch_Get_Args return Uint32_T;  -- pebble.h:2420
   pragma Import (C, Launch_Get_Args, "launch_get_args");


   subtype Anon3606_Tm_Zone_Array is Interfaces.C.char_array (0 .. 5);
   type Tm is record
      Tm_Sec    : aliased int;  -- pebble.h:6601
      Tm_Min    : aliased int;  -- pebble.h:6602
      Tm_Hour   : aliased int;  -- pebble.h:6603
      Tm_Mday   : aliased int;  -- pebble.h:6604
      Tm_Mon    : aliased int;  -- pebble.h:6605
      Tm_Year   : aliased int;  -- pebble.h:6606
      Tm_Wday   : aliased int;  -- pebble.h:6607
      Tm_Yday   : aliased int;  -- pebble.h:6608
      Tm_Isdst  : aliased int;  -- pebble.h:6609
      Tm_Gmtoff : aliased int;  -- pebble.h:6611
      Tm_Zone   : aliased Anon3606_Tm_Zone_Array;  -- pebble.h:6612
   end record;
   pragma Convention (C_Pass_By_Copy, Tm);  -- pebble.h:6600

   function Strftime
     (Arg1 : Strings_Interface.Chars_Ptr;
      Arg2 : Size_T;
      Arg3 : Strings_Interface.Chars_Ptr;
      Arg4 : Opaque_Ptr) return int;  -- pebble.h:6622
   pragma Import (C, Strftime, "strftime");

   function Localtime
     (Arg1 : access Time_T) return access Tm;  -- pebble.h:6629
   pragma Import (C, Localtime, "localtime");

   function Gmtime (Arg1 : access Time_T) return access Tm;  -- pebble.h:6635
   pragma Import (C, Gmtime, "gmtime");

   function Mktime (Arg1 : access Tm) return Time_T;  -- pebble.h:6641
   pragma Import (C, Mktime, "mktime");

   function Time_Ms
     (Arg1 : access Time_T;
      Arg2 : access Uint16_T) return Uint16_T;  -- pebble.h:6672
   pragma Import (C, Time_Ms, "time_ms");

private
   type Window is new Opaque_Ptr;
   Null_Window : constant Window := Window (System.Null_Address);
end Pebble;
