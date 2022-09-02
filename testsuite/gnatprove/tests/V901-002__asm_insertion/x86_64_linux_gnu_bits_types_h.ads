pragma Ada_2012;
pragma Style_Checks (Off);

with Interfaces.C; use Interfaces.C;
with System;
with Interfaces.C.Strings;

package x86_64_linux_gnu_bits_types_h is

   subtype uu_u_char is unsigned_char;  -- /usr/include/x86_64-linux-gnu/bits/types.h:31

   subtype uu_u_short is unsigned_short;  -- /usr/include/x86_64-linux-gnu/bits/types.h:32

   subtype uu_u_int is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:33

   subtype uu_u_long is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:34

   subtype uu_int8_t is signed_char;  -- /usr/include/x86_64-linux-gnu/bits/types.h:37

   subtype uu_uint8_t is unsigned_char;  -- /usr/include/x86_64-linux-gnu/bits/types.h:38

   subtype uu_int16_t is short;  -- /usr/include/x86_64-linux-gnu/bits/types.h:39

   subtype uu_uint16_t is unsigned_short;  -- /usr/include/x86_64-linux-gnu/bits/types.h:40

   subtype uu_int32_t is int;  -- /usr/include/x86_64-linux-gnu/bits/types.h:41

   subtype uu_uint32_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:42

   subtype uu_int64_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:44

   subtype uu_uint64_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:45

   subtype uu_int_least8_t is uu_int8_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:52

   subtype uu_uint_least8_t is uu_uint8_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:53

   subtype uu_int_least16_t is uu_int16_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:54

   subtype uu_uint_least16_t is uu_uint16_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:55

   subtype uu_int_least32_t is uu_int32_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:56

   subtype uu_uint_least32_t is uu_uint32_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:57

   subtype uu_int_least64_t is uu_int64_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:58

   subtype uu_uint_least64_t is uu_uint64_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:59

   subtype uu_quad_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:63

   subtype uu_u_quad_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:64

   subtype uu_intmax_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:72

   subtype uu_uintmax_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:73

   subtype uu_dev_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:145

   subtype uu_uid_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:146

   subtype uu_gid_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:147

   subtype uu_ino_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:148

   subtype uu_ino64_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:149

   subtype uu_mode_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:150

   subtype uu_nlink_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:151

   subtype uu_off_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:152

   subtype uu_off64_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:153

   subtype uu_pid_t is int;  -- /usr/include/x86_64-linux-gnu/bits/types.h:154

   --  skipped anonymous struct anon_0

   type uu_fsid_t_uu_val_array is array (0 .. 1) of aliased int;
   type uu_fsid_t is record
      uu_val : aliased uu_fsid_t_uu_val_array;  -- /usr/include/x86_64-linux-gnu/bits/types.h:155
   end record
   with Convention => C_Pass_By_Copy;  -- /usr/include/x86_64-linux-gnu/bits/types.h:155

   subtype uu_clock_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:156

   subtype uu_rlim_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:157

   subtype uu_rlim64_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:158

   subtype uu_id_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:159

   subtype uu_time_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:160

   subtype uu_useconds_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:161

   subtype uu_suseconds_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:162

   subtype uu_daddr_t is int;  -- /usr/include/x86_64-linux-gnu/bits/types.h:164

   subtype uu_key_t is int;  -- /usr/include/x86_64-linux-gnu/bits/types.h:165

   subtype uu_clockid_t is int;  -- /usr/include/x86_64-linux-gnu/bits/types.h:168

   type uu_timer_t is new System.Address;  -- /usr/include/x86_64-linux-gnu/bits/types.h:171

   subtype uu_blksize_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:174

   subtype uu_blkcnt_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:179

   subtype uu_blkcnt64_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:180

   subtype uu_fsblkcnt_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:183

   subtype uu_fsblkcnt64_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:184

   subtype uu_fsfilcnt_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:187

   subtype uu_fsfilcnt64_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:188

   subtype uu_fsword_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:191

   subtype uu_ssize_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:193

   subtype uu_syscall_slong_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:196

   subtype uu_syscall_ulong_t is unsigned_long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:198

   subtype uu_loff_t is uu_off64_t;  -- /usr/include/x86_64-linux-gnu/bits/types.h:202

   type uu_caddr_t is new Interfaces.C.Strings.chars_ptr;  -- /usr/include/x86_64-linux-gnu/bits/types.h:203

   subtype uu_intptr_t is long;  -- /usr/include/x86_64-linux-gnu/bits/types.h:206

   subtype uu_socklen_t is unsigned;  -- /usr/include/x86_64-linux-gnu/bits/types.h:209

   subtype uu_sig_atomic_t is int;  -- /usr/include/x86_64-linux-gnu/bits/types.h:214

end x86_64_linux_gnu_bits_types_h;
