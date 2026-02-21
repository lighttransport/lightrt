CXX = g++
CXXFLAGS = -std=c++17 -O3 -Wall -Wextra -fno-rtti -fno-exceptions \
           -I.. -I../viewer -I../viewer/third_party -I../viewer/common
LDFLAGS = -lgdi32 -luser32 -lkernel32 -lpthread -lshell32 -mwindows

TARGET = viewer_windows.exe
SOURCES = viewer_windows.cc ../viewer/common/viewer_common.cc ../lightrt.cc
OBJECTS = $(notdir $(SOURCES:.cc=.o))

# Detect AVX2 support (default: enabled on x86-64)
ifneq ($(NO_AVX2),1)
CXXFLAGS += -mavx2 -mfma
endif

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(CXX) $(OBJECTS) -o $(TARGET) $(LDFLAGS)

viewer_windows.o: viewer_windows.cc
	$(CXX) $(CXXFLAGS) -c $< -o $@

viewer_common.o: ../viewer/common/viewer_common.cc
	$(CXX) $(CXXFLAGS) -c $< -o $@

lightrt.o: ../lightrt.cc
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(OBJECTS) $(TARGET)

.PHONY: all clean
