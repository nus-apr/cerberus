--TEST--
New testcase
--FILE--
<?php

class sw {

    public function stream_open($path, $mode, $options, &$opened_path) {
        return true;
    }

	public function stream_stat() {
		return array(
            'mtime' => $this->undefined,
        );
	}

}
class sww {

    public function stream_open($path, $mode, $options, &$opened_path) {
        return true;
    }

	public function stream_stat() {
		return array(
            'mtime' => 6,
        );
	}

}

stream_wrapper_register('sx', 'sw') or die('failed');

fstat(fopen('sx://test', 'r'));

$s[] = 1; //  Cannot use a scalar value as an array

print_r($s);

stream_wrapper_register('sxx', 'sww') or die('failed');
print_r( fstat(fopen('sxx://test', 'r'))['mtime'] );?>
--EXPECT--
Notice: Undefined property: sw::$undefined in /home/fanl/Workspace/prophet/build/benchmarks/php-src-1f49902/php-1f49902.php on line 11
Array
(
    [0] => 1
)
6
