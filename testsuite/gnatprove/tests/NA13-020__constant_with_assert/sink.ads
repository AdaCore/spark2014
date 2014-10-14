with System;
with SK;

package Sink
is
	The_Sink : SK.Word64
		with Async_Readers, Effective_Writes, Volatile, Address => System'To_Address (16#1234567800#);
end Sink;
