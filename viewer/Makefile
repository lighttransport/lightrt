CXX = g++
CXXFLAGS = -std=c++17 -O3 -Wall -Wextra -fno-rtti -fno-exceptions -I.. -I. -Ithird_party -mavx2 -mfma -DVK_NO_PROTOTYPES
LDFLAGS = -lglfw -ldl -lpthread

TARGET = viewer
SOURCES = viewer.cc vk_loader.cc ../lightrt.cc
OBJECTS = $(SOURCES:.cc=.o)

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(CXX) $(OBJECTS) -o $(TARGET) $(LDFLAGS)

%.o: %.cc
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(OBJECTS) $(TARGET)

.PHONY: all clean
